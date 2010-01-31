'''
Dynamic Taint Mode for Python.
User level module.
Juan Jose Conti <jjconti@gmail.com>
'''
ENDS = False
KEYS  = [XSS, SQLI, OSI, II] = range(4)
KEYS = set(KEYS)

from pprint import pprint
import pdb
import inspect
import sys

def ends_execution(b=True):
    global ENDS
    ENDS = b
    
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
    
def t_string(s):
	return taint(s)
	
def t_list(l):
	return [t_(x) for x in l]

def t_tuple(l):
	return tuple([t_(x) for x in l])
	
def t_dict(d):
    klass = type(d) # es comun que los frameworks extiendan dict con 
                    # nuevos metodos, como en web.py
    return klass([(k, t_(v)) for k,v in d.items()])
	
def t_(o):
    if isinstance(o, basestring):
        return t_string(o)
    elif isinstance(o, list):
        return t_list(o)
    elif isinstance(o, tuple):
        return t_tuple(o)
    elif isinstance(o, dict):
        return t_dict(o)
    else:
        return o
			
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
                args[n] = t_(args[n])
            for n in nkwargs:
                kwargs[n] = t_(kwargs[n])
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
        return t_(r)
    return inner

def validator(v, nargs=[], nkwargs=[]):
    '''
    Mark a function or methos as capable to validate its input.
    
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
                    if v in a.taints:
                        a.taints.remove(v)
            return r
        return inner
    return _validator
    
def cleaner(v):
    '''
    Mark a function or methos as capable to clean its input.
    
    v is removed from the returned value .taints set.
    '''
    def _cleaner(f):    
        def inner(*args, **kwargs):
            r = f(*args, **kwargs)
            if v in r.taints:
                r.taints.remove(v)
                                      # la logica es que si luego de aplicar
            return r                  # una funcion limpiadora, el resultado es
        return inner                  # el mismo y est tenía v en .taints,
    return _cleaner                   # entonces esta bien borrar v de ahi.
    
def ssink(v=None, reached=reached):
    '''
    Mark a function or method as sensitive to tainted data.
    
    If it is called with a value with v in .taints
    (or a non empty .taints v is None),
    it's not executed and reached is executed instead.
    '''
    def _solve(a, f, args, kwargs):
        if ENDS:
            return reached(a)
        else:
            reached(a)
            return f(*args, **kwargs)
                        
    def _ssink(f):
        def inner(*args, **kwargs):
            allargs = set(args) | set(kwargs.values())
            if v is None:   # sensitive to ALL
                for a in allargs:
                    if hasattr(a, 'taints') and a.taints:
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
    Tells if a value o, STR instance, is tainted for the given vul.
    
    If v is None, test if o.taints is not empty.
    '''
    if not isinstance(o, STR):
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
    if var == '':
        return var
    var = STR(var)
    if v:
        var.taints.add(v)
        return var
    else:
        var.taints.update(KEYS)
        return var
            
def update_taints(o, taints):
    if isinstance(o, STR):
        o.taints.update(taints)
    elif isinstance(o, list):
        [update_taints(x, taints) for x in o]        
    elif isinstance(o, tuple):
        [update_taints(x, taints) for x in o]
    elif isinstance(o, dict):
        for k, v in o.iteritems():
            update_taints(v, taints)

def wrap2(cls, method):
    def _w(self, *args, **kwargs):
        r = i_(method(self, *args, **kwargs))
        update_taints(r, self.taints)
        for a in args:
            if hasattr(a, 'taints'):
                update_taints(r, a.taints)
        for k,v in kwargs.items():
            if hasattr(v, 'taints'):
                update_taints(r, a.taints)
        return r
    return _w
        
def i_string(s):
	return STR(s)
	
def i_list(l):
	return [i_(x) for x in l]

def i_tuple(l):
	return tuple([i_(x) for x in l])
	
def i_dict(d):
    klass = type(d) # es comun que los frameworks extiendan dict con 
                    # nuevos metodos, como en web.py
    return klass([(k, i_(v)) for k,v in d.items()])
	
def i_(o):
    if isinstance(o, basestring):
        return i_string(o)
    elif isinstance(o, list):
        return i_list(o)
    elif isinstance(o, tuple):
        return i_tuple(o)
    elif isinstance(o, dict):
        return i_dict(o)
    else:
        return o

import inspect
    
methods = ['__add__', '__getitem__', '__getslice__', '__mod__', '__mul__', '__rmod__', '__rmul__', 'capitalize', 'center', 'expandtabs', 'join', 'ljust', 'lower', 'lstrip', 'partition', 'replace', 'rjust', 'rpartition', 'rsplit', 'rstrip', 'split', 'splitlines', 'strip', 'swapcase', 'title', 'translate', 'upper', 'zfill']

def taint_class(klass):
    class tklass(klass):
        def __new__(cls, *args, **kwargs):
            self = super(tklass, cls).__new__(cls, *args, **kwargs)
            self.taints = set()
            return self
    d = klass.__dict__
    for name, attr in [(m, d[m]) for m in methods]:
        if inspect.ismethod(attr) or inspect.ismethoddescriptor(attr):
            setattr(tklass, name, wrap2(tklass, attr))
    setattr(tklass, '__radd__', lambda self, other: tklass.__add__(tklass(other), self))
    
    return tklass      


STR = taint_class(str)        
