'''
Dynamic Taint Mode for Python.
User level module.
Juan Jose Conti <jjconti@gmail.com>
'''
KEYS  = [XSS, SQLI, OSI, II] = range(4)
TAINTED = dict([(x, set()) for x in KEYS])

from pprint import pprint
import pdb
import inspect
import sys

def reached(t, v=None):
    '''
    Execute if a tainted value reaches a sensitive sink
    for the vulnerability v.
    '''
    frame = sys._getframe(2)
    filename = inspect.getfile(frame)
    lno = frame.f_lineno - 1
    print "=" * 79
    print "Violacion en la linea %d del archivo %s." % (lno, filename)
    #print "Valor manchado: %s." % t
    print '-' * 79
    lineas = inspect.findsource(frame)[0]
    lineas = ['    %s' % l for l in lineas]
    lineas[lno] = '--> ' + lineas[lno][4:]
    lineas = lineas[lno - 3: lno + 3]
    print "".join(lineas) 
    print "=" * 79
    
def t_string(s):
	return taint(s)
	
def t_list(l):
	return [t_(x) for x in l]

def t_dict(d):
	return dict([(k, t_(v)) for k,v in d.items()])
	
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
            for n in nargs:
                args[n] = t_(args[n])
            for n in nkwargs:
                kwargs[n] = t_(kwargs[n])
            r = f(*args, **kwargs)
            return r
        return inner
    return _untrusted_params
    
def untrusted(f):
    '''
    Mark a function or method as untrusted.
    
    The returned value will be tainted for all the types of taint.
    '''     
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        return t_(r)
    return inner
        
def cleaner(v):
    '''
    Mark a function or methos as capable to clean its input.
    
    If v is provied, the returned value is removed from the TAINTED[v] set.
    If not, it's removed from all the sets int TAINTED.
    '''
    def _cleaner(f):    
        def inner(*args, **kwargs):
            global TAINTED
            r = f(*args, **kwargs)
            if r in TAINTED[v]:
                TAINTED[v].remove(r)  # la logica es que si luego de aplicar
            return r                  # una funcion limpiadora, el resultado es
        return inner                  # el mismo y este estaba en TAINTED, 
    return _cleaner                   # entonces esta bien borrarlo de ahi.
    
def ssink(v=None, reached=reached):
    '''
    Mark a function or method as sensitive to tainted data.
    
    If it is called with a value present at TAINTED[v]
    (or any TAINTED set if v is None),
    it's not executed and reached is executed instead.
    '''
    def _ssinc(f):
        def inner(*args, **kwargs):
            allargs = set(args) | set(kwargs.values())
            if v is None:   # sensitive to ALL
                tainted = reduce(lambda a, b: a | b, 
                                 [x for x in TAINTED.values()], set())
                for a in allargs:
                    if a in tainted:
                        return reached(a)
                else:
                    return f(*args, **kwargs)
            else:
                for a in allargs:
                    if a in TAINTED[v]:
                        return reached(a, v=v)
                else:
                    return f(*args, **kwargs)
        return inner            
    return _ssinc
    
def tainted(o, v=None):
    '''
    Tells if a value o is tainted for the given vul.
    
    If vul is None, the value is searched in avery TAINTED set.
    '''
    if v:
        vset = TAINTED.get(v)
        if vset:
            return o in vset
        else:
            return False
    for s in TAINTED.values():
        if o in s:
            return True
    return False

def taint(var, v=None):
    '''
    Helper function for taint variables.
    '''
    var = STR(var)
    if v:
        vset = TAINTED.get(v)
        if vset:
            vset.add(var)
            return var
    else:
        for s in TAINTED.values():
            s.add(var)
        return var
            
            
class STR(str):
    '''
    Extends str class to provide extra capabilities that make it sutable to
    trac taints over operations.
    '''
    def __str__(self):
        return self

    def __add__(self, other):
        r = super(STR, self).__add__(other)
        r = STR(r)
        for s in TAINTED.values():
            if self in s or other in s:
                s.add(r)
        return r

    def __radd__(self, other):
        return STR.__add__(STR(other), self)
     
    def __getslice__(self, i, j):
        r = super(STR, self).__getslice__(i, j)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r) 
        return r

    def __getitem__(self, y):
        r = super(STR, self).__getitem__(y)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def __mod__(self, y):
        r = super(STR, self).__mod__(y)
        r = STR(r)
        for s in TAINTED.values():
            if self in s or y in s:
                s.add(r)
        return r    
        
    def __mul__(self, y):
        r = super(STR, self).__mul__(y)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r            

    def __rmod__(self, other):
        return STR.__mod__(STR(other), self)
        
    def __rmul__(self, other):
        return STR.__mul__(STR(self), other)

    def capitalize(self):
        r = super(STR, self).capitalize()
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def center(self, width, fillchar=' '):
        r = super(STR, self).center(width, fillchar)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    # decode, encode ?
    
    def expandtabs(self, tabsize=8):
        r = super(STR, self).expandtabs(tabsize)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r    

    def join(self, y):
        r = super(STR, self).join(y)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def ljust(self, width, fillchar=' '):
        r = super(STR, self).ljust(width, fillchar)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def lower(self):
        r = super(STR, self).lower()
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def lstrip(self, chars=' '):
        r = super(STR, self).lstrip(chars)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
            
    def partition(self, sep):
        head, sep, tail = super(STR, self).partition(sep)
        head, sep, tail = STR(head), STR(sep), STR(tail)
        for s in TAINTED.values():
            if self in s:
                s.add(head)
                if sep:
                    s.add(sep)
                if tail:
                    s.add(tail)
        return head, sep, tail

    def replace(self, old, new, count=-1):
        r = super(STR, self).replace(old, new, count)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r

    def rjust(self, width, fillchar=' '):
        r = super(STR, self).rjust(width, fillchar)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def rpartition(self, sep):
        head, sep, tail = super(STR, self).rpartition(sep)
        head, sep, tail = STR(head), STR(sep), STR(tail)
        for s in TAINTED.values():
            if self in s:
                s.add(head)
                if sep:
                    s.add(sep)
                if tail:
                    s.add(tail)
        return head, sep, tail
        
    def rsplit(self, sep=' ', maxsplit=-1):
        aList = super(STR, self).rsplit(sep, maxsplit)
        aList = [STR(l) for l in aList]
        for s in TAINTED.values():
            if self in s:
                [s.add(x) for x in aList]
        return aList
        
    def rstrip(self, chars=' '):
        r = super(STR, self).rstrip(chars)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r        

    def split(self, sep=' ', maxsplit=-1):
        aList = super(STR, self).split(sep, maxsplit)
        aList = [STR(l) for l in aList]
        for s in TAINTED.values():
            if self in s:
                [s.add(x) for x in aList]
        return aList

    def splitlines(self, keepends=False):
        aList = super(STR, self).splitlines(keepends)
        aList = [STR(l) for l in aList]
        for s in TAINTED.values():
            if self in s:
                [s.add(x) for x in aList]
        return aList

    def strip(self, chars=' '):
        r = super(STR, self).strip(chars)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r

    def swapcase(self):
        r = super(STR, self).swapcase()
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r

    def title(self):
        r = super(STR, self).title()
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
        
    def translate(self, table, deletechars=''):
        r = super(STR, self).translate(table, deletechars)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r      
        
    def upper(self):
        r = super(STR, self).upper()
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r

    def zfill(self, width):
        r = super(STR, self).zfill(width)
        r = STR(r)
        for s in TAINTED.values():
            if self in s:
                s.add(r)
        return r
