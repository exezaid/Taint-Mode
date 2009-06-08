from dyntaint import *
import random
import unittest

def reached(v=None):
    return False  

@untrusted
def some_input():
    '''Some random input from the 'outside'.'''
    return "#%&#$%<--&" * random.randint(1, 10)

@cleaner(SQLI)
def cleanSQLI(s):
    '''Dummy SQL injection cleaner.'''
    return s.replace("--", "")

@cleaner(XSS)
def cleanXSS(s):
    '''Dummy XSS cleaner.'''
    return s.replace("<", "&lt;")

@ssink(reached=reached)
def saveDB(valor):
    '''Dummy save in database function.'''
    return True
    
class TestDifferenteVulnerabilities(unittest.TestCase):

    def test_tainted(self):
        '''a tainted value reaches a sensitive sink.'''
            
        i = some_input()
        self.assertFalse(saveDB(i))

    def test_tainted_not_clean_anough(self):
        '''a partial tainted value reaches a full sensitive sink.'''

        i = some_input()
        self.assertFalse(saveDB(cleanSQLI(i)))

    def test_not_tainted(self):
        '''an SQLI-cleaned value reaches a SQLI-sensitive sink. It's all right.'''

        @ssink(v=SQLI, reached=reached)
        def saveDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(saveDB(cleanSQLI(i)))


class TestTaintFlow(unittest.TestCase):

    def test_right_concatenation_not_cleaned(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''

        @ssink(v=SQLI, reached=reached)
        def saveDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(saveDB(i + "hohoho"))

    def test_left_concatenation_not_cleaned(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''

        @ssink(v=SQLI, reached=reached)
        def saveDB(valor):
            return True
            
        i = some_input()
        self.assertFalse(saveDB("hohoho" + i))
                    
    def test_right_concatenation(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted.'''

        @ssink(v=SQLI, reached=reached)
        def saveDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(saveDB(cleanSQLI(i + "hohoho")))

    def test_left_concatenation(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted.'''
    
        @ssink(v=SQLI, reached=reached)
        def saveDB(valor):
            return True
            
        i = some_input()
        self.assertTrue(saveDB(cleanSQLI("hohoho" + i)))
                                                    
if __name__ == '__main__':
    unittest.main()

