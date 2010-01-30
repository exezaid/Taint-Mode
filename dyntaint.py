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

def t_dict(d):
    klass = type(d) # es comun que los frameworks extiendan dict con 
                    # nuevos metodos, como en web.py
    return klass([(k, t_(v)) for k,v in d.items()])
	
def t_(o):
	if isinstance(o, basestring):
		return t_string(o)
	elif isinstance(o, list):
		return t_list(o)
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
            

def wrap(self, cls, method):
    def _w(*args, **kwargs):
        sup = getattr(super(cls, self), method)
        r = cls(sup(*args, **kwargs))
        r.taints.update(self.taints)
        for a in args:
            if hasattr(a, 'taints'):
                r.taints.update(a.taints)
        for k,v in kwargs.items():
            if hasattr(v, 'taints'):
                r.taints.update(v.taints)                
        print r
        return r
    return _w
    
    
class STR(str):
    '''
    Extends str class to provide extra capabilities that make it sutable to
    trac taints over operations.
    '''
    
    def __new__(cls, s):
        self = super(STR, cls).__new__(cls, s)
        self.taints = set()
        return self
    
    def __str__(self):
        return super(STR, self).__str__()   # REVISAR si esto no proboca
                                            # un error al perder la clase del o

    def __add__(self, other):
        return wrap(self, STR, '__add__')(other)

    def __radd__(self, other):
        return STR.__add__(STR(other), self)
     
    def __getslice__(self, i, j):
        return wrap(self, STR, '__getslice__')(i, j)

    def __getitem__(self, y):
        return wrap(self, STR, '__getitem__')(y)
                
    def __mod__(self, y):
        return wrap(self, STR, '__mod__')(y)   
        
    def __mul__(self, y):
        return wrap(self, STR, '__mul__')(y)           

    def __rmod__(self, other):
        return wrap(self, STR, '__rmod__')(other)   
        
    def __rmul__(self, other):
        return wrap(self, STR, '__rmul__')(other)

    def capitalize(self):
        return wrap(self, STR, 'capitalize')()   
        
    def center(self, width, fillchar=' '):
        return wrap(self, STR, 'center')(width, fillchar)   
        
    # decode, encode ?
    
    def expandtabs(self, tabsize=8):
        return wrap(self, STR, 'expandtabs')(tabsize)   
        
    def join(self, y):
        return wrap(self, STR, 'join')(y)
                
    def ljust(self, width, fillchar=' '):
        return wrap(self, STR, 'ljust')(width, fillchar)
        
    def lower(self):
        return wrap(self, STR, 'lower')()
        
    def lstrip(self, chars=' '):
        return wrap(self, STR, 'lstrip')(chars)
            
    def partition(self, sep):       # WARN: no se puede aplicar wrap por que r no es str
        head, sep, tail = super(STR, self).partition(sep)
        head, sep, tail = STR(head), STR(sep), STR(tail)
        head.taints.update(self.taints)
        sep.taints.update(self.taints)
        tail.taints.update(self.taints)
        # should the original sep be tested too?
        return head, sep, tail

    def replace(self, old, new, count=-1):
        return wrap(self, STR, 'replace')(old, new, count)

    def rjust(self, width, fillchar=' '):
        return wrap(self, STR, 'rjust')(width, fillchar)    # revistar test ljust
                
    def rpartition(self, sep):
        head, sep, tail = super(STR, self).rpartition(sep)
        head, sep, tail = STR(head), STR(sep), STR(tail)
        head.taints.update(self.taints)
        sep.taints.update(self.taints)
        tail.taints.update(self.taints)
        #verificar si hay casos en que sep este manchado y como tratarlo
        return head, sep, tail
        
    def rsplit(self, sep=' ', maxsplit=-1):
        aList = super(STR, self).rsplit(sep, maxsplit)
        aList = [STR(l) for l in aList]
        [r.taints.update(self.taints) for r in aList]
        return aList
        
    def rstrip(self, chars=' '):
        return wrap(self, STR, 'rstrip')(chars)       

    def split(self, sep=' ', maxsplit=-1):
        aList = super(STR, self).split(sep, maxsplit)
        aList = [STR(l) for l in aList]
        [r.taints.update(self.taints) for r in aList]
        return aList

    def splitlines(self, keepends=False):
        aList = super(STR, self).splitlines(keepends)
        aList = [STR(l) for l in aList]
        [r.taints.update(self.taints) for r in aList]
        return aList

    def strip(self, chars=' '):
        return wrap(self, STR, 'strip')(chars)

    def swapcase(self):
        return wrap(self, STR, 'swapcase')()

    def title(self):
        return wrap(self, STR, 'title')()
                
    def translate(self, table, deletechars=''):
        return wrap(self, STR, 'translate')(table, deletechars)     
        
    def upper(self):
        return wrap(self, STR, 'upper')()

    def zfill(self, width):
        return wrap(self, STR, 'zfill')(width)
