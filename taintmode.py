'''
Dynamic Taint Mode for Python.
User level module.
Juan Jose Conti <jjconti@gmail.com>
'''

import pdb
import inspect
import sys
from itertools import chain

          
ENDS = False
RAISES = False
KEYS  = [XSS, SQLI, OSI, II] = range(4)
TAGS = set(KEYS)

__all__ = ['tainted', 'taint', 'untrusted', 'untrusted_args', 'ssink', 
           'cleaner', 'STR', 'INT', 'FLOAT', 'UNICODE', 'chr', 'ord', 'len',
           'ends_execution', 'XSS', 'SQLI', 'OSI', 'II']
           
class TaintException(Exception):
    pass
    
def ends_execution(b=True):
    global ENDS
    ENDS = b
        
def propagate_func(original):
    def inner (*args, **kwargs):
        t = set()
        for a in args:
            mapt(a, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))
        for v in kwargs.values():
            mapt(v, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))
        r  = original(*args,**kwargs)
        if t == set([]):
            return r
        r = taint_aware(r, t)
        return r
    return inner
   
len = propagate_func(len)     
ord = propagate_func(ord)
chr = propagate_func(chr)
	
def mapt_list(l, f, c):
	return [mapt(x, f, c) for x in l]

def mapt_tuple(t, f, c):
	return tuple([mapt(x, f, c) for x in t])

def mapt_set(s, f, c):
    return set([mapt(x, f, c) for x in s])
    
def mapt_dict(d, f, c):
    klass = type(d) # It's quite common for frameworks to extend dict
                    # with useful new methdos - i.e. web.py
    return klass([(k, mapt(v, f, c)) for k,v in d.items()])
	
def mapt(o, f, check=lambda o: type(o) in tclasses.keys()):
    if check(o):
        return f(o)
    elif isinstance(o, list):
        return mapt_list(o, f, check)
    elif isinstance(o, tuple):
        return mapt_tuple(o, f, check)
    elif isinstance(o, set):
        return mapt_set(o, f, check)        
    elif isinstance(o, dict):
        return mapt_dict(o, f, check)
    else:
        return o

# Decorators
			
def untrusted_args(nargs=[], nkwargs=[]):
    '''
    Mark a function or method that would recive untrusted values.
    
    nargs is a list of positions. Positional arguments in that position will be 
    tainted for all the types of taint.
	nkwargs is a list of strings. Keyword arguments for those keys will be
	tainted for all the types of taint.
    '''
    def _untrusted_args(f):
        def inner(*args, **kwargs):
            args = list(args)   # args is a tuple
            for n in nargs:
                args[n] = mapt(args[n], taint)
            for n in nkwargs:
                kwargs[n] = mapt(kwargs[n], taint)
            r = f(*args, **kwargs)
            return r
        return inner
    return _untrusted_args
    
def untrusted(f):
    '''
    Mark a function or method as untrusted.
    
    The returned value will be tainted for all the types of taint.
    '''     
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        return taint_aware(r, TAGS)
    return inner

def validator(v, nargs=[], nkwargs=[]):
    '''
    Mark a function or method as capable to validate its input.
    
    nargs is a list of positions. Positional arguments in that positions are
    the ones validated.
	nkwargs is a list of strings. Keyword arguments for those keys are the ones
	validated.
    If the function returns True, v will be removed from the the validated
    inpunt .taints set.
    '''
    def _validator(f):
        def inner(*args, **kwargs):
            r = f(*args, **kwargs)
            if r:
                tovalid = set([args[n] for n in nargs]) | set([kwargs[n] for n in nkwargs])
                for a in tovalid:
                    mapt(a, remove_taint(v), lambda o: True)
            return r
        return inner
    return _validator
    
def remove_taint(v):
    def _remove(o):
        if hasattr(o, 'taints'):
            o.taints.discard(v)
    return _remove

def remove_tags(r, v):
    mapt(r, remove_taint(v), lambda o: True)
    
def cleaner(v):
    '''
    Mark a function or methos as capable to clean its input.
    
    v is removed from the returned value.
    '''
    def _cleaner(f):    
        def inner(*args, **kwargs):
            r = f(*args, **kwargs)
            remove_tags(r, v)
            return r
        return inner
    return _cleaner

def reached(t, v=None):
    '''
    Execute if a tainted value reaches a sensitive sink
    for the vulnerability v.
    '''
    frame = sys._getframe(3)
    filename = inspect.getfile(frame)
    lno = frame.f_lineno
    print "=" * 79
    print "Violacion en la linea %d del archivo %s" % (lno, filename)
    print "Valor manchado: %s" % t
    print '-' * 79
    lineas = inspect.findsource(frame)[0]   # cambiar a getsourceline cuando el parche de gg este incorporado
    lineas = ['    %s' % l for l in lineas]
    lno = lno - 1
    lineas[lno] = '--> ' + lineas[lno][4:]
    lineas = lineas[lno - 3: lno + 3]
    print "".join(lineas) 
    print "=" * 79
        
def ssink(v=None, reached=reached):
    '''
    Mark a function or method as sensitive to tainted data.
    
    If it is called with a value with v in .taints
    (or a non empty .taints v is None),
    it's not executed and reached is executed instead.
    '''
    def _solve(a, f, args, kwargs):
        if ENDS:
            if RAISES:
                reached(a)
                raise TaintException
            else:
                return reached(a)
        else:
            reached(a)
            return f(*args, **kwargs)
                        
    def _ssink(f):
        def inner(*args, **kwargs):
            allargs = chain(args, kwargs.values())
            if v is None:   # sensitive to ALL
                for a in allargs:
                    if hasattr(a, 'taints') and a.taints:   # cambiar por algo que revise los niveles de dict/lists
                        return _solve(a, f, args, kwargs)
            else:
                for a in allargs:
                    if hasattr(a, 'taints') and v in a.taints:
                        return _solve(a, f, args, kwargs)
            return f(*args, **kwargs)
        return inner
    return _ssink
    
def tainted(o, v=None):
    '''
    Tells if a value o, ant tclass instance, is tainted for the given vul.
    
    If v is None, test if o.taints is not empty.
    '''
    if not hasattr(o, 'taints'):
        return False
    if v:
        return v in o.taints
    if o.taints:
        return True
    return False

def taint(var, v=None):
    '''
    Helper function for taint variables.
    Empty string can't be tainted.
    '''
    if var == '':   #sure of this?
        return var
    var = tclass(var)
    if v:
        var.taints.add(v)
        return var
    else:
        var.taints.update(TAGS)
        return var

# Taint-aware classes

def collect_tags(s, t):
    '''Collect tags from a source s into a target t.'''
    mapt(s, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))

def update_tags(r, t):
    mapt(r, lambda o: o.taints.update(t), lambda o: hasattr(o, 'taints'))    
  
def taint_aware(r, ts=set()):
    r = mapt(r, tclass)
    update_tags(r, ts)
    return r
    
def propagate_method(method):
    def _w(self, *args, **kwargs):
        r = method(self, *args, **kwargs)
        r = taint_aware(r)
        t = set()
        for a in args:
            collect_tags(a, t)
        for v in kwargs.values():
            collect_tags(v, t)
        t.update(self.taints)         
        update_tags(r, t)
        return r
    return _w

import inspect

def taint_class(klass, methods):
    class tklass(klass):
        def __new__(cls, *args, **kwargs):
            self = super(tklass, cls).__new__(cls, *args, **kwargs)
            self.taints = set()
            return self
    d = klass.__dict__
    for name, attr in [(m, d[m]) for m in methods]:
        if inspect.ismethod(attr) or inspect.ismethoddescriptor(attr):
            setattr(tklass, name, propagate_method(attr))
    if '__add__' in methods and '__radd__' not in methods:   # str has no __radd__ method, it does
        setattr(tklass, '__radd__', lambda self, other: tklass.__add__(tklass(other), self))
    
    tklass.__name__ = klass.__name__.upper()
    return tklass

dont_override = set(['__repr__', '__cmp__', '__getattribute__', '__new__', '__init__','__nonzero__',
                 '__class__', '__reduce__', '__reduce_ex__'])

def attributes(klass):
    a = set(klass.__dict__.keys())
    return a - dont_override
    
str_methods = attributes(str)
unicode_methods = attributes(unicode)
int_methods = attributes(int)
float_methods = attributes(float)

# TODO: utilizar type para crear las clases y asi poder ponerles un nombre
STR = taint_class(str, str_methods)
UNICODE = taint_class(unicode, unicode_methods)
INT = taint_class(int, int_methods)
FLOAT = taint_class(float, float_methods)

tclasses = {str: STR, int: INT, float: FLOAT, unicode: UNICODE}

def tclass(o):
    '''Tainted instance factory.'''
    klass = type(o)
    if klass in tclasses.keys():
        return tclasses[klass](o)
    else:
        raise KeyError        
