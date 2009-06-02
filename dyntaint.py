TAINTED = set()

def untrusted(f):
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        TAINTED.add(r)
        return r
    return inner
    
def cleaner(f):    
    def inner(*args, **kwargs):
        global TAINTED
        r = f(*args, **kwargs)
        TAINTED -= set(args) | set(kwargs.values())
        return r
    return inner
    
def ssinc(f):
    def inner(*args, **kwargs):
        if not (set(args) | set(kwargs.values())) & TAINTED:
            return f(*args, **kwargs)
        else:
            print "WARNING"
    return inner            
    
