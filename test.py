from dyntaint import *
import unittest

def reached(v=None):
    return False  

@untrusted
def some_input(value="some input from the outside"):
    '''Some random input from the 'outside'.'''
    return value

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

# Para some_input() se debe usar siempre un valor nuevo para evitar
# que el orden en que se ejecutan los tests y el hecho de que TAINTED sea
# global afecte el resultado.

class TestDifferenteVulnerabilities(unittest.TestCase):

    def test_tainted(self):
        '''a tainted value reaches a sensitive sink.'''
            
        i = some_input('a r v r a s s')    # join with tainted value as argument, not suported.)
        self.assertFalse(saveDB1(i))

    def test_tainted_not_clean_anough(self):
        '''a partial tainted value reaches a full sensitive sink.'''

        i = some_input('a p t v r a f s s')
        self.assertFalse(saveDB1(cleanSQLI(i)))

    def test_not_tainted(self):
        '''an SQLI-cleaned value reaches a SQLI-sensitive sink. It's all right.'''
            
        i = some_input('a s c v r a s s s i a r')
        self.assertTrue(saveDB2(cleanSQLI(i)))


class TestTaintFlow(unittest.TestCase):
        
    def test_right_concatenation_not_cleaned(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
            
        i = some_input('right concatenation')
        self.assertFalse(saveDB2(i + "hohoho"))

    def test_left_concatenation_not_cleaned(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted. If not cleaned, the taint reaches the sink.'''
            
        i = some_input('left concatenation')
        self.assertFalse(saveDB2("hohoho" + i))
                    
    def test_right_concatenation(self):
        '''a tainted value is right concatenated with a non tainted value.
        The result is tainted.'''
            
        i = some_input('clean right concatenation')
        self.assertTrue(saveDB2(cleanSQLI(i + "hohoho")))

    def test_left_concatenation(self):
        '''a tainted value is left concatenated with a non tainted value.
        The result is tainted.'''
            
        i = some_input('clean left concatenation')
        self.assertTrue(saveDB2(cleanSQLI("hohoho" + i)))

    def test_indexing_not_cleaned(self):
        '''if you get an item from a tainted value, te item is also tainted.'''
            
        i = some_input('indexing')
        self.assertFalse(saveDB2(i[4]))
        
    def test_indexing(self):
        '''if you get an item from a tainted value, te item is also tainted.'''
            
        i = some_input('clean indexing')
        self.assertTrue(saveDB2(cleanSQLI(i[4])))

    def test_mul_not_cleaned(self):
        '''if s is tainted, s * n is also tainted.'''
            
        i = some_input('multi')
        self.assertFalse(saveDB2(i * 8))
        
    def test_mul(self):
        '''if s is tainted, s * n is also tainted.'''
            
        i = some_input('clean multi')
        self.assertTrue(saveDB2(cleanSQLI(i * 8)))

    def test_left_mul_not_cleaned(self):
        '''if s is tainted, n * s is also tainted.'''
            
        i = some_input('left multi')
        self.assertFalse(saveDB2(8 * i))
        
    def test_left_mul(self):
        '''if s is tainted, n * s is also tainted.'''
            
        i = some_input('clean left multi')
        self.assertTrue(saveDB2(cleanSQLI(8 * i)))

    def test_slice_not_cleaned(self):
        '''if  you slice a tainted value, the slice also tainted.'''
            
        i = some_input('take a slice')
        self.assertFalse(saveDB2(i[2:5]))
        
    def test_slice(self):
        '''if  you slice a tainted value, the slice also tainted.'''
            
        i = some_input('clean teke a slice')
        self.assertTrue(saveDB2(cleanSQLI(i[2:5] )))

    # tests for public str methdos
    
    def test_join_not_cleaned(self):
        '''if s is tainted, s.join(aLista) is also tainted.'''
            
        i = some_input('join')
        self.assertFalse(saveDB2(i.join(['_', '_', '_'])))
        
    def test_join(self):
        '''if s is tainted, s.join(aLista) is also tainted.'''
            
        i = some_input('clean join')
        self.assertTrue(saveDB2(cleanSQLI(i.join(['_', '_', '_']))))  

    # join with tainted value as argument, not suported.

    def test_capitalize_not_cleaned(self):
        '''if s is tainted. s.capitalize() is also tainted.'''
        
        i = some_input('capitalize')
        self.assertFalse(saveDB2(i.capitalize()))

    def test_capitalize(self):
        '''if s is tainted. s.capitalize() is also tainted.'''
        
        i = some_input('clean capitalize')
        self.assertTrue(saveDB2(cleanSQLI(i.capitalize())))

    def test_center_not_cleaned(self):
        '''if s is tainted. s.center(n) is also tainted.'''
        
        i = some_input('center')
        self.assertFalse(saveDB2(i.center(6)))

    def test_center(self):
        '''if s is tainted. s.center(n) is also tainted.'''
        
        i = some_input('clean center')
        self.assertTrue(saveDB2(cleanSQLI(i.center(6))))
 
    def test_expandtabs_not_cleaned(self):
        '''if s is tainted. s.expandtabs(n) is also tainted.'''
        
        i = some_input('\t')
        self.assertFalse(saveDB2(i.expandtabs(4)))

    def test_expandtabs(self):
        '''if s is tainted. s.expandtabs(n) is also tainted.'''
        
        i = some_input('\tclean\t')
        self.assertTrue(saveDB2(cleanSQLI(i.expandtabs(4))))

    def test_ljust_not_cleaned(self):
        '''if s is tainted. s.ljust(n) is also tainted.'''
        
        i = some_input('left just')
        self.assertFalse(saveDB2(i.ljust(42)))

    def test_ljust(self):
        '''if s is tainted. s.ljust(n) is also tainted.'''
        
        i = some_input('clean left just')
        self.assertTrue(saveDB2(cleanSQLI(i.ljust(42))))

    def test_lower_not_cleaned(self):
        '''if s is tainted. s.lower() is also tainted.'''
        
        i = some_input("NOT LOWER")
        self.assertFalse(saveDB2(i.lower()))

    def test_lower(self):
        '''if s is tainted. s.lower() is also tainted.'''
        
        i = some_input("CLEAN NOT LOWER")
        self.assertTrue(saveDB2(cleanSQLI(i.lower())))

    def test_lstrip_not_cleaned(self):
        '''if s is tainted. s.lstrip() is also tainted.'''
        
        i = some_input("       left spaces")
        self.assertFalse(saveDB2(i.lstrip()))

    def test_lstrip(self):
        '''if s is tainted. s.lstrip() is also tainted.'''
        
        i = some_input("       left spaces and clean")
        self.assertTrue(saveDB2(cleanSQLI(i.lstrip())))

    def test_partition_not_cleaned(self):
        '''s.partition(sep) -> head, sep, tail. If s is tainted, 
        head, sep and tail are also tainted.'''
        
        i = some_input("sepa/rated")
        h, s, t = i.partition('/')
        self.assertFalse(saveDB2(h))
        self.assertFalse(saveDB2(s))        
        self.assertFalse(saveDB2(t))

    def test_partition(self):
        '''s.partition(sep) -> head, sep, tail. If s is tainted, 
        head, sep and tail are also tainted.'''
        
        i = some_input("clean sepa/rated")
        h, s, t = i.partition('/')
        self.assertTrue(saveDB2(cleanSQLI(h)))
        self.assertTrue(saveDB2(cleanSQLI(s)))        
        self.assertTrue(saveDB2(cleanSQLI(t)))

    def test_replace_not_cleaned(self):
        '''if s is tainted. s.replace(old, new[, count]) is also tainted.'''
        
        i = some_input("a_a_a_a_a")
        self.assertFalse(saveDB2(i.replace('_', ' ')))

    def test_replace(self):
        '''if s is tainted. s.replace(old, new[, count]) is also tainted.'''
        
        i = some_input("clean_a_a_a_a_a")
        self.assertTrue(saveDB2(cleanSQLI(i.replace('_', ' '))))         

    def test_replace_with_count_not_cleaned(self):
        '''if s is tainted. s.replace(old, new[, count]) is also tainted.'''
        
        i = some_input("a_a_a_a_a_count")
        self.assertFalse(saveDB2(i.replace('_', ' ', 2)))

    def test_replace_with_count(self):
        '''if s is tainted. s.replace(old, new[, count]) is also tainted.'''
        
        i = some_input("clean_a_a_a_a_a_count")
        self.assertTrue(saveDB2(cleanSQLI(i.replace('_', ' ', 2))))  

    # replace with tainted value as argument, not suported.
        
class TestTAINTED(unittest.TestCase):   

    def test_all_set(self):
        n = some_input('test all set')
        self.assertTrue(n in TAINTED[SQLI])
        self.assertTrue(n in TAINTED[XSS])

    def test_in_one_set(self):
        n = some_input('test in one set')
        n = cleanSQLI(n)
        self.assertFalse(n in TAINTED[SQLI])
        self.assertTrue(n in TAINTED[XSS])
        
    def test_in_no_set(self):
        n = some_input('test in no set')
        n = cleanSQLI(n)
        n = cleanXSS(n)
        self.assertFalse(n in TAINTED[SQLI])
        self.assertFalse(n in TAINTED[XSS])    

class TestTainted(unittest.TestCase):

    def test_taint(self):
        x = 'taint'
        self.assertFalse(tainted(x))
        i = some_input(x)
        self.assertTrue(tainted(i))

    def test_taint_vul(self):
        x = 'taint_vul'
        self.assertFalse(tainted(x))
        i = some_input(x)
        self.assertTrue(tainted(i, vul=XSS))
        self.assertTrue(tainted(i, vul=SQLI))
        i = cleanSQLI(i)
        self.assertTrue(tainted(i, vul=XSS))
        self.assertFalse(tainted(i, vul=SQLI))

    def test_taint_vul2(self):
        '''If the givven vul argument is not a valid KEY,
        return False.'''
        x = 'taint_vul2'
        self.assertFalse(tainted(x))
        i = some_input(x)
        self.assertFalse(tainted(i, vul=100))
                        
class TestSink(unittest.TestCase):
            
    def test_false_all(self):
        n = some_input('test false all')
        self.assertFalse(saveDB1(n))
        self.assertFalse(saveDB2(n))
        self.assertFalse(saveDB3(n))

    def test_one(self):
        n = some_input('test one')
        n = cleanSQLI(n)
        self.assertFalse(saveDB1(n))
        self.assertTrue(saveDB2(n))
        self.assertFalse(saveDB3(n))
        
    def test_true_all(self):
        n = some_input('test true all')
        n = cleanSQLI(n)
        n = cleanXSS(n)
        self.assertTrue(saveDB1(n))
        self.assertTrue(saveDB2(n))
        self.assertTrue(saveDB3(n))
        
         
if __name__ == '__main__':
    unittest.main()

