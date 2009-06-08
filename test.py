from dyntaint import *
import random
import unittest

def reached(v=None):
    return False  

@untrusted
def some_input():
    return "#%&#$%<--&" * random.randint(1, 10)

@cleaner(SQLI)
def limpiarSQLi(s):
    return s.replace("--", "")

@cleaner(XSS)
def limpiarSQLi(s):
    return s.replace("<", "&lt;")

@ssink(reached=reached)
def guardarDB(valor):
    return True
    
class TestDifferenteVulnerabilities(unittest.TestCase):

    def setup(self):
        pass
        
    def test_tainted(self):
        '''a tainted value reaches a sensitive sink.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @ssink(reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(guardarDB(i))

    def test_tainted_not_clean_anough(self):
        '''a partial tainted value reaches a full sensitive sink.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(guardarDB(cleanSQLI(i)))

    def test_not_tainted(self):
        '''an SQLI-cleaned value reaches a SQLI-sensitive sink. It's all right.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(v=SQLI, reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(guardarDB(cleanSQLI(i)))


class TestTaintFlow(unittest.TestCase):

    def setup(self):
        pass

    def test_right_concatenation_not_cleaned(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(v=SQLI, reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(guardarDB(i + "hohoho"))

    def test_left_concatenation_not_cleaned(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(v=SQLI, reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(guardarDB("hohoho" + i))
                    
    def test_right_concatenation(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(v=SQLI, reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(guardarDB(cleanSQLI(i + "hohoho")))

    def test_left_concatenation(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted.'''
        
        def reached(v=None):
            return False
        
        @untrusted
        def some_input():
            return "#%&#$%<--&" * random.randint(1, 10)

        @cleaner(SQLI)
        def cleanSQLI(s):
            return s.replace("--", "")
    
        @ssink(v=SQLI, reached=reached)
        def guardarDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(guardarDB(cleanSQLI("hohoho" + i)))
                                                    
if __name__ == '__main__':
    unittest.main()

