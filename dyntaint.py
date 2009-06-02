KEYS  = [XSS, SQLI] = range(2)
TAINTED = dict([(x, set()) for x in KEYS])


def untrusted(f):
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
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
    
def ssinc(v=None):
    def _ssinc(f):
        def inner(*args, **kwargs):
            if v is None:   # sensitive to ALL
                if not (set(args) | set(kwargs.values()) & reduce(lambda a, b: a | b, [x for x in TAINTED.values()], set())):
                    return f(*args, **kwargs)
                else:
                    print "WARNING ALL"
            else:
                if not (set(args) | set(kwargs.values())) & TAINTED[v]:
                    return f(*args, **kwargs)
                else:
                    print "WARNING", v
        return inner            
    return _ssinc

