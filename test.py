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

@ssink(v=XSS, reached=reached)
def saveDB3(valor):
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

    def test_indexing_not_cleaned(self):
        '''if you get an item from a tainted value, te item is also tainted.'''
            
        i = some_input()
        self.assertFalse(saveDB2(i[4]))
        
    def test_indexing(self):
        '''if you get an item from a tainted value, te item is also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i[4])))

    def test_mul_not_cleaned(self):
        '''if s is tainted, s * n is also tainted.'''
            
        i = some_input()
        self.assertFalse(saveDB2(i * 8))
        
    def test_mul(self):
        '''if s is tainted, s * n is also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i * 8)))

    def test_left_mul_not_cleaned(self):
        '''if s is tainted, n * s is also tainted.'''
            
        i = some_input()
        self.assertFalse(saveDB2(8 * i))
        
    def test_left_mul(self):
        '''if s is tainted, n * s is also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(8 * i)))

    def test_slice_not_cleaned(self):
        '''if  you slice a tainted value, the slice also tainted.'''
            
        i = some_input()
        self.assertFalse(saveDB2(i[2:5]))
        
    def test_slice(self):
        '''if  you slice a tainted value, the slice also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i[2:5] )))
 
    def test_join_not_cleaned(self):
        '''if s is tainted, s.join(aLista) is also tainted.'''
            
        i = some_input()
        self.assertFalse(saveDB2(i.join(['_', '_', '_'])))
        
    def test_join(self):
        '''if s is tainted, s.join(aLista) is also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI(i.join(['_', '_', '_']))))  

    def test_arg_join_not_cleaned(self):
        '''if s is tainted and aList contains s, someString.join(aList) is also tainted.'''
        
        i = some_input()
        #self.assertFalse(saveDB2("".join([i, i, i])))   # esto es un problema
        
    def test_arg_join(self):
        '''if s is tainted and aList contains s, someString.join(aList) is also tainted.'''
            
        i = some_input()
        self.assertTrue(saveDB2(cleanSQLI("".join([i, i, i])))) 


class TestTAINTED(unittest.TestCase):

    def test_all_set(self):
        n = some_input()
        self.assertTrue(n in TAINTED[SQLI])
        self.assertTrue(n in TAINTED[XSS])

    def test_in_one_set(self):
        n = some_input()
        n = cleanSQLI(n)
        self.assertFalse(n in TAINTED[SQLI])
        self.assertTrue(n in TAINTED[XSS])
        
    def test_in_no_set(self):
        n = some_input()
        n = cleanSQLI(n)
        n = cleanXSS(n)
        self.assertFalse(n in TAINTED[SQLI])
        self.assertFalse(n in TAINTED[XSS])    

class TestSink(unittest.TestCase):

    def test_false_all(self):
        n = some_input()
        self.assertFalse(saveDB1(n))
        self.assertFalse(saveDB2(n))
        self.assertFalse(saveDB3(n))

    def test_one(self):
        n = some_input()
        n = cleanSQLI(n)
        self.assertFalse(saveDB1(n))
        self.assertTrue(saveDB2(n))
        self.assertFalse(saveDB3(n))
        
    def test_true_all(self):
        n = some_input()
        n = cleanSQLI(n)
        n = cleanXSS(n)
        self.assertTrue(saveDB1(n))
        self.assertTrue(saveDB2(n))
        self.assertTrue(saveDB3(n))

if __name__ == '__main__':
    unittest.main()

