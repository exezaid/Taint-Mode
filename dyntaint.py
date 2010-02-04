'''
Dynamic Taint Mode for Python.
User level module.
Juan Jose Conti <jjconti@gmail.com>
'''
ENDS = False
RAISES = False
KEYS  = [XSS, SQLI, OSI, II] = range(4)
KEYS = set(KEYS)

class TaintException(Exception):
    pass
    
import pdb
import inspect
import sys
from itertools import chain

def propagate_func(original):
    def inner (*args, **kwargs):
        t = set()
        for a in args:
            mapt(a, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))
        for k,v in kwargs.items():
            mapt(v, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))
        r  = original(*args,**kwargs)
        if t == set([]):
            return r
        r = mapt(r, tclass)
        r.taints.update(t)
        return r
    return inner
   
# This alternative implementation of
# len let INT to be returned by len
len = propagate_func(len)     
ord = propagate_func(ord)
chr = propagate_func(chr)
#-----------------------------------------------------------------------------#

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
	
def mapt_list(l, f, c):
	return [mapt(x, f, c) for x in l]

def mapt_tuple(t, f, c):
	return tuple([mapt(x, f, c) for x in t])

def mapt_set(s, f, c):
    return set([mapt(x, f, c) for x in s])
    
def mapt_dict(d, f, c):
    klass = type(d) # es comun que los frameworks extiendan dict con 
                    # nuevos metodos, como en web.py
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
        return mapt(r, taint)
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
                    
def cleaner(v):
    '''
    Mark a function or methos as capable to clean its input.
    
    v is removed from the returned value.
    '''
    def _cleaner(f):    
        def inner(*args, **kwargs):
            r = f(*args, **kwargs)
            mapt(r, remove_taint(v), lambda o: True)
            return r
        return inner
    return _cleaner
    
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
    if var == '':   #REVEER
        return var
    var = tclass(var)
    if v:
        var.taints.add(v)
        return var
    else:
        var.taints.update(KEYS)
        return var

def collect_tags(s, t):
    '''Collect tags from a source s into a target t.'''
    mapt(s, lambda o: t.update(o.taints), lambda o: hasattr(o, 'taints'))

def update_taints(r, t):
    mapt(r, lambda o: o.taints.update(t), lambda o: hasattr(o, 'taints'))    
    
def propagate_method(method):
    def _w(self, *args, **kwargs):
        r = mapt(method(self, *args, **kwargs), tclass)
        t = set()
        for a in args:
            collect_tags(a, t)
        for k,v in kwargs.items():
            collect_tags(v, t)
        t.update(self.taints)         
        update_taints(r, t)
        return r
    return _w

import inspect

def taint_class1(klass, methods):
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
    
    return tklass      

dont_override = ['__repr__', '__cmp__', '__getattribute__', '__new__', '__init__','__nonzero__',
                 '__class__', '__reduce__', '__reduce_ex__']

def taint_class(klass):
    class tklass(klass):
        def __new__(cls, *args, **kwargs):
            self = super(tklass, cls).__new__(cls, *args, **kwargs)
            self.taints = set()
            return self
    d = klass.__dict__
    for name, attr in klass.__dict__.iteritems():#[(m, d[m]) for m in methods]:
        if (inspect.ismethod(attr) or inspect.ismethoddescriptor(attr)) and name not in dont_override:
            try:
                setattr(tklass, name, propagate_method(attr))
            except:
                print "No se modifica", name                
    if '__add__' in klass.__dict__.keys() and '__radd__' not in klass.__dict__.keys():   # str has no __radd__ method, it does
        setattr(tklass, '__radd__', lambda self, other: tklass.__add__(tklass(other), self))
    
    return tklass 
    
str_methods = ['__add__', '__contains__', '__doc__', '__eq__', '__format__', '__ge__', '__getitem__', '__getnewargs__', '__getslice__', '__gt__', '__hash__', '__le__', '__len__', '__lt__', '__mod__', '__mul__', '__ne__', '__rmod__', '__rmul__', '__str__', '_formatter_field_name_split', '_formatter_parser', 'capitalize', 'center', 'count', 'decode', 'encode', 'endswith', 'expandtabs', 'find', 'format', 'index', 'isalnum', 'isalpha', 'isdigit', 'islower', 'isspace', 'istitle', 'isupper', 'join', 'ljust', 'lower', 'lstrip', 'partition', 'replace', 'rfind', 'rindex', 'rjust', 'rpartition', 'rsplit', 'rstrip', 'split', 'splitlines', 'startswith', 'strip', 'swapcase', 'title', 'translate', 'upper', 'zfill']

unicode_methods = ['__add__', '__contains__', '__doc__', '__eq__', '__format__', '__ge__', '__getitem__', '__getnewargs__', '__getslice__', '__gt__', '__hash__', '__le__', '__len__', '__lt__', '__mod__', '__mul__', '__ne__', '__rmod__', '__rmul__', '__str__', '_formatter_field_name_split', '_formatter_parser', 'capitalize', 'center', 'count', 'decode', 'encode', 'endswith', 'expandtabs', 'find', 'format', 'index', 'isalnum', 'isalpha', 'isdecimal', 'isdigit', 'islower', 'isnumeric', 'isspace', 'istitle', 'isupper', 'join', 'ljust', 'lower', 'lstrip', 'partition', 'replace', 'rfind', 'rindex', 'rjust', 'rpartition', 'rsplit', 'rstrip', 'split', 'splitlines', 'startswith', 'strip', 'swapcase', 'title', 'translate', 'upper', 'zfill']


# ojo, hay algunos atribujos que no se pueden setear, los voy borrando de aqui
# en el futuro usar dir() y manejar la excepcion
# elimino: __repr__ __cmp__ __getattribute__ __new__ __init__
# '__nonzero__' pide q sea bool o int
int_methods = ['__abs__', '__add__', '__and__', '__coerce__', '__div__', '__divmod__', '__doc__', '__float__',
'__floordiv__', '__format__', '__getnewargs__', '__hash__', '__hex__', '__index__', '__int__',
'__invert__', '__long__', '__lshift__', '__mod__', '__mul__', '__neg__', '__oct__', '__or__',
'__pos__', '__pow__', '__radd__', '__rand__', '__rdiv__', '__rdivmod__', '__rfloordiv__', '__rlshift__', '__rmod__',
'__rmul__', '__ror__', '__rpow__', '__rrshift__', '__rshift__', '__rsub__', '__rtruediv__', '__rxor__', '__str__', '__sub__', '__truediv__', '__trunc__', '__xor__', 'conjugate', 'denominator', 'imag', 'numerator', 'real']

# nose pueden sobreescribir
# __class__  '__reduce__', '__reduce_ex__'
# TODO: Comparar listas para ver que metodos no se incluyen
float_methods = ['__abs__', '__add__', '__coerce__', '__div__', '__divmod__', '__doc__', '__eq__', '__float__', '__floordiv__', '__format__', '__ge__', '__getformat__', '__getnewargs__', '__gt__', '__hash__', '__int__', '__le__', '__long__', '__lt__', '__mod__', '__mul__', '__ne__', '__neg__', '__nonzero__', '__pos__', '__pow__', '__radd__', '__rdiv__', '__rdivmod__', '__repr__', '__rfloordiv__', '__rmod__', '__rmul__', '__rpow__', '__rsub__', '__rtruediv__', '__setformat__', '__str__', '__sub__', '__truediv__', '__trunc__', 'as_integer_ratio', 'conjugate', 'fromhex', 'hex', 'imag', 'is_integer', 'real']

# TODO: utilizar type para crear las clases y asi poder ponerles un nombre
STR = taint_class(str)#, str_methods)
UNICODE = taint_class(unicode)#, unicode_methods)
INT = taint_class(int)#, int_methods)
FLOAT = taint_class(float)#, float_methods)

tclasses = {str: STR, int: INT, float: FLOAT, unicode: UNICODE}

def tclass(o):
    '''Tainted instance factory.'''
    klass = type(o)
    if klass in tclasses.keys():
        return tclasses[klass](o)
    else:
        raise KeyError        
