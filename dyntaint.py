'''
Dynamic Taint Mode for Python.
User level module.
Juan Jose Conti <jjconti@gmail.com>
'''
KEYS  = [XSS, SQLI, OSI, II] = range(4)
TAINTED = dict([(x, set()) for x in KEYS])

from pprint import pprint

def reached(v=None):
    '''Execute if a tainted value reaches a sensitive sink
    for the vulnerability v. '''
    if v:
        print "WARNING", v
    else:
        print "WARNING ALL"

def untrusted_params(nargs):
    def _untrusted_params(f):
        def inner(*args, **kwargs):
            #for p in (set([args[x] for x in nargs]) | set(kwargs.values())):   dict are unhasheables
            for p in [args[x] for x in nargs] + list(kwargs.values()):
                if isinstance(p, basestring):
                    p = STR(p)
                    [s.add(p) for s in TAINTED.values()] # unstrusted for ALL
                elif isinstance(p, dict):
                    for i in p.values():
                        if isinstance(i, basestring):
                            i = STR(i)
                            [s.add(i) for s in TAINTED.values()] # unstrusted for ALL                    
            r = f(*args, **kwargs)            
            return r
        return inner
    return _untrusted_params
    
def untrusted(f):
    '''
    Mark a function or method as untrusted.
    The returned value will me tainted for all the types of taint.
    '''
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        r = STR(r)
        [s.add(r) for s in TAINTED.values()] # unstrusted for ALL
        return r
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
            #TAINTED[v] -= set(args) | set(kwargs.values())
            if r in TAINTED[v]:
                TAINTED[v].remove(r)    #OJO ACA
            return r
        return inner
    return _cleaner
    
def ssink(v=None, reached=reached):
    '''
    Mark a function or method as sensitive to tainted data.
    If it is called with a value present at TAINTED[v] (or any TAINTED set if v is None),
    it's not executed and reached is executed instead.
    '''
    def _ssinc(f):
        def inner(*args, **kwargs):
            if v is None:   # sensitive to ALL
                if not ((set(args) | set(kwargs.values())) & 
                           reduce(lambda a, b: a | b, [x for x in TAINTED.values()], set())):
                    return f(*args, **kwargs)
                else:
                    return reached()
            else:
                if not (set(args) | set(kwargs.values())) & TAINTED[v]:
                    return f(*args, **kwargs)
                else:
                    return reached(v)
        return inner            
    return _ssinc
    
def tainted(o, vul=None):
    '''
    Tells if a value o is tainted for the given vul. 
    If vul is None, the value is searched in avery TAINTED set.
    '''
    if vul:
        vulset = TAINTED.get(vul)
        if vulset:
            return o in vulset
        else:
            return False
    for s in TAINTED.values():
        if o in s:
            return True
    return False

def taint(var, vul=None):
    '''
    Helper function for taint variables.
    '''
    var = STR(var)
    if vul:
        vulset = TAINTED.get(vul)
        if vulset:
            vulset.add(var)
            return var
    else:
        for s in TAINTED.values():
            s.add(var)
        return var
            
            
class STR(str):
    '''
    Extends str class to provide extra capabilities that make it sutable to trac taints
    over operations.
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
        return STR.__add__(STR(other), self)    # a better way for this?
     
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
            if self in s:
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
        return STR.__mod__(STR(other), self)    # a better way for this?
        
    def __rmul__(self, other):
        return STR.__mul__(STR(self), other)    # a better way for this?        

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
