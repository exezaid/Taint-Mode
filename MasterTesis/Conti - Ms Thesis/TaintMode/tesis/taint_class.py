def taint_class(klass, methods):
    class tklass(klass):
      def __new__(cls, *args, **kwargs):
          self = super(tklass, cls).__new__(cls, *args, **kwargs)
          self.taints = set()
          return self
    d = klass.__dict__
    for name, attr in [(m, d[m]) for m in methods]:
        if inspect.ismethod(attr) or 
	   inspect.ismethoddescriptor(attr):
              setattr(tklass, name, propagate_method(attr))
    if '__add__' in methods and '__radd__' not in methods:   
        setattr(tklass, '__radd__', 
	        lambda self, other: tklass.__add__(tklass(other), 
		self))
    return tklass      

