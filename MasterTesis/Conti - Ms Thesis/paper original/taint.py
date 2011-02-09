def untrusted(f):
    def inner(*args, **kwargs):
        r = f(*args, **kwargs)
        return taint_aware(r, TAGS)
    return inner