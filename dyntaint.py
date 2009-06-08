KEYS  = [XSS, SQLI] = range(2)
TAINTED = dict([(x, set()) for x in KEYS])

def reached(v=None):
    '''Execute if a tainted value reaches a sensitive sink
    for the vulnerability v. '''
    if v:
        print "WARNING", v
    else:
        print "WARNING ALL"

def untrusted(f):
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        r = STR(r)
        [s.add(r) for s in TAINTED.values()] # unstrusted for ALL
        return r
    return inner
    
def cleaner(v):
    def _cleaner(f):    
        def inner(*args, **kwargs):
            global TAINTED
            r = f(*args, **kwargs)
            TAINTED[v] -= set(args) | set(kwargs.values())
            return r
        return inner
    return _cleaner
    
def ssink(v=None, reached=reached):
    def _ssinc(f):
        def inner(*args, **kwargs):
            if v is None:   # sensitive to ALL
                if not (set(args) | set(kwargs.values()) & reduce(lambda a, b: a | b, [x for x in TAINTED.values()], set())):
                    return f(*args, **kwargs)
                else:
                    reached()
            else:
                if not (set(args) | set(kwargs.values())) & TAINTED[v]:
                    return f(*args, **kwargs)
                else:
                    reached(v)
        return inner            
    return _ssinc
    
# String operations
# lo siguiente puede hacerse con un decorador.
class STR(str):

    def __add__(self, other):
        r = super(STR, self).__add__(other)
        r = STR(r)
        for v, s in TAINTED.items():
            if self in s or other in s:
                s.add(r)
        return r

    def __radd__(self, other):
        return STR.__add__(STR(other), self)    # a better way for this?
     
    def __getslice__(self, i, j):
        r = super(STR, self).__getslice__(i, j)
        r = STR(r)
        for v, s in TAINTED.items():
            if self in s:
                s.add(r) 
        return r

    def __getitem__(self, y):
        r = super(STR, self).__getitem__(y)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r
        
    def __mod__(self, y):
        r = super(STR, self).__mod__(y)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r    
        
    def __mul__(self, y):
        r = super(STR, self).__mul__(y)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r            

    def __rmod__(self, other):
        return STR.__mod__(STR(other), self)    # a better way for this?
        
    def __rmul__(self, other):
        return STR.__mul__(STR(self), other)    # a better way for this?        
        
    def __join__(self, y):
        r = super(STR, self).__join__(y)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r

    def capitalize(self):
        r = super(STR, self).capitalize()
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r
        
    def center(self, width, fillchar=' '):
        r = super(STR, self).center(width, fillchar)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r
        
    # decode, encode ?
    
    def expandtabs(self, tabsize=8):
        r = super(STR, self).expandtabs(tabsize)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r    
        
    def ljust(self, width, fillchar=' '):
        r = super(STR, self).ljust(width, fillchar)
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r
        
    def lower(self):
        r = super(STR, self).lower()
        r = STR(r)
        for v,s in TAINTED.items():
            if self in s:
                s.add(r)
        return r
        
    # lstrip
    
    def partition(self, sep):
        head, sep, tail = super(STR, self).partition(sep)
        head, sep, tail = STR(h), STR(s), STR(t)
        for v,s in TAINTED.items():
            if self in s:
                s.add(head)
                if sep:
                    s.add(sep)
                if tail:
                    s.add(tail)
        return head, sep, tail
