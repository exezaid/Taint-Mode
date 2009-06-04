from dyntaint import *

# Mark unstrusted sources

@untrusted
def obtener_numero(mensaje="Ingrese un numero: "):
    n = raw_input(mensaje)
    return n

@cleaner(SQLI)
def limpiarSQLi(s):
    '''lo limpie, creeme.'''
    return s

@ssinc(SQLI)
def guardarDB(valor):
    print "Guardando en la BD:", valor

@ssinc(XSS)
def mostrarPagina(valor):
    print '<html>%s</html>' % (valor,)

@ssinc()
def sensible(valor):
    print valor

if __name__ == '__main__':
    n = obtener_numero()
    # n esta manchada
    guardarDB(n)
    mostrarPagina(n)
    m1 = n + "hola"
    # m1 esta manchada
    guardarDB(m1)
    m2 = "chau " + n
    # m2 esta manchada
    guardarDB(m2)
    o = n[0]    
    # o esta manchada
    mostrarPagina(o)
    p = o * 8      
    # p esta machada
    mostrarPagina(p)     
    q = (n * 10)[2:4]
    # q esta manchada
    sensible(q)
    r = 10 * q
    # r esta mancha
    sensible(r)
    s = n.join([' ', ' ', ' '])
    # s esta manchada
    sensible(s)
    s2 = "".join([n,n,n])   
    #s2 esta manchada
    sensible(s2)
