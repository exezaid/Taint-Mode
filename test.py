from dyntaint import *
import unittest

def reached(v=None):
    return False  

@untrusted
def some_input():
    '''Some random input from the 'outside'.'''
    return "input from the outside"

@cleaner(SQLI)
def cleanSQLI(s):
    '''Dummy SQL injection cleaner.'''
    return s.replace("--", "")

@cleaner(XSS)
def cleanXSS(s):
    '''Dummy XSS cleaner.'''
    return s.replace("<", "&lt;")

@ssink(reached=reached)
def saveDB1(valor):
    '''Dummy save in database function. Sensitive to all vulnerabilities.'''
    return True

@ssink(v=SQLI, reached=reached)
def saveDB2(valor):
    '''Dummy save in database function. Only sensitive to SQL injection.'''
    return True
    
class TestDifferenteVulnerabilities(unittest.TestCase):

    def test_tainted(self):
        '''a tainted value reaches a sensitive sink.'''
            
        i = some_input()
        self.assertFalse(saveDB1(i))

    def test_tainted_not_clean_anough(self):
        '''a partial tainted value reaches a full sensitive sink.'''

        i = some_input()
        self.assertFalse(saveDB1(cleanSQLI(i)))

    def test_not_tainted(self):
        '''an SQLI-cleaned value reaches a SQLI-sensitive sink. It's all right.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i)))


class TestTaintFlow(unittest.TestCase):

    def test_right_concatenation_not_cleaned(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
            
        i = some_input()
        self.assertFalse(saveDB2(i + "hohoho"))

    def test_left_concatenation_not_cleaned(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
            
        i = some_input()
        self.assertFalse(saveDB2("hohoho" + i))
                    
    def test_right_concatenation(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i + "hohoho")))

    def test_left_concatenation(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI("hohoho" + i)))
                                                    
if __name__ == '__main__':
    unittest.main()

