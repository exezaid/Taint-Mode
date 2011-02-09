def propagate_func(original):
    def inner (*args, **kwargs):
        t = set()
        for a in args:
            collect_tags(a,t)
        for v in kwargs.values():
            collect_tags(v,t)
        r  = original(*args,**kwargs)
        if t == set([]):
            return r
        return taint_aware(r,t)
    return inner