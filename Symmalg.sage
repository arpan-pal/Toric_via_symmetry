def monomial_generator(variables, degree):
    '''
    This function takes set of variables and a degree as input, 
    and returns a list consisting of monomilas of desired degree in the given set of variables.
    variables = list or tuple consisting of variables
    degree = desired degree of the monomials
    '''
    n_vars = len(variables)
    degs = list(WeightedIntegerVectors(degree,[1 for i in range(n_vars)]))
    monomials = []
    for d in degs:
        mon = 1
        for i in range(n_vars):
            mon *= variables[i]^d[i]
        monomials.append(mon)
    return monomials

def lie_derivative_mono(monomial, g, n = 0):
    '''
    This function takes a monomial and a matrix `g` as input and returns Lie derivative of the monomial with respect to `g`.
    monomial = a monomial
    g = a matrix, with respect to which the Lie derivative is calculated
    n = number of variables in the ambient ring, optional argument
    '''
    if n == 0:
        n_vars = len(monomial.parent().gens())
    else:
        n_vars = n
    R = monomial.parent()
    X = matrix(R,n_vars, 1, R.gens()[:n_vars])
    gen_index = {}
    for l in range(len(R.gens())):
        gen_index[R.gens()[l]] = l
    der = 0
    for x in monomial.factor():
        l = (g[gen_index[x[0]],:]*X)[0,0]
        der+= l*R(monomial/x[0])*x[1]
    return der

def lie_derivative_poly(poly, g, n = 0):
    '''
    This function takes a polynomial and a matrix `g` as input, and returns Lie derivative of the polynomial with respect to `g`.
    polynomial = a polynomial
    g = a matrix, with respect to which the Lie derivative is calculated
    n = number of variables in the ambient ring, optional argument
    '''
    if n == 0:
        n_vars = len(poly.parent().gens())
    else:
        n_vars = n
    der = 0
    for mon, coef in list(zip(poly.monomials(),poly.coefficients())):
        der+= lie_derivative_mono(mon,g, n_vars)*coef
    return der

def poly_to_vec(polynomial, n = 0, degree = 0):
    '''
    This function takes a polynomial as input and returns its vector representation as output.
    polynomial = a polynomial
    n = number of variables in the ambient polynomial ring
    degree = degree of the polynomial
    '''
    R = polynomial.parent()
    if n == 0:
        n_vars = len(R.gens())
    else:
        n_vars = n
    if degree == 0:
        d = polynomial.degree()
    else:
        d = degree
    n_2 = binomial(n_vars+d-1,d)
    monomials = monomial_generator(R.gens()[:n_vars], d)
    vec = [0 for j in range(n_2)]
    for i in range(n_2):
        vec[i] = polynomial.coefficient(monomials[i])
    return vec



def symmalg_homo(generators, n = 0):
    ''' 
    This function takes generators of a homogeneous prime ideal as input.
    Then computes and returns the symmetry Lie algebra of the ideal generated by the polynomials in `generatos`. 
    This function also assumes that all the generating polynomials of the ideal homogeneous and of same degree.
    generatots = generators of the ideal
    n = number of variables in the ambient ring
    '''
    S = generators[0].parent()
    if n!=0:
        n_vars = n
    else:
        n_vars = len(S.gens())
    var =[str(t) for t in S.gens()[:n_vars]]
    var+= ['g%i%i'%(i,j) for i in range(1,n_vars+1) for j in range(1,n_vars+1)]
    R = PolynomialRing(QQ, var)
    R.inject_variables()
    gens = [R(g) for g in generators]
    d = gens[0].degree()
    g = matrix(R,n_vars,n_vars,R.gens()[n_vars:])
    gens_vecs = [poly_to_vec(gen, n_vars) for gen in gens]
    der_gens_vecs = [poly_to_vec(lie_derivative_poly(gen, g, n_vars), n_vars, d) for gen in gens]
    matrices = [matrix(gens_vecs+[i]) for i in der_gens_vecs]
    eqns = set()
    for M in matrices:
        for eqn in M.minors(len(gens)+1):
            if eqn!= 0:
                eqns.add(eqn)
    eqns = list(eqns)
    ker = []
    for eqn in eqns:
        l = [eqn.coefficient(gij) for gij in R.gens()[n_vars:]]
        ker.append(l)
    K = matrix(ker)
    rows = K.pivot_rows()
    K = K[rows,:]
    K_ker = K.right_kernel_matrix()
    L = [matrix(QQ,n_vars,n_vars,r) for r in K_ker.rows()]
    LieI = gap.LieAlgebra(gap.Rationals,L)
    print('\nA basis of the Lie algebra consists of the following matrices:\n')
    show(L)
    return LieI


def symmalg(generators, n = 0):
    ''' 
    This function takes generators of a homogeneous prime ideal as input.
    Then computes and returns the symmetry Lie algebra of the ideal generated by the polynomials in `generatos`.
    generatots = generators of the ideal
    n = number of variables in the ambient ring
    '''
    S = generators[0].parent()
    if n!=0:
        n_vars = n
    else:
        n_vars = len(S.gens())
    var =[str(t) for t in S.gens()[:n_vars]]
    R = PolynomialRing(QQ, var)
    R.inject_variables()
    gens = [R(g) for g in generators]
    d = max([g.degree() for g in gens])
    L = []
    for g in gens:
        monomials = monomial_generator(R.gens()[:n_vars], d-g.degree())
        for m in monomials:
            L.append(g*m)
    M = matrix(R, [poly_to_vec(l, n_vars, d) for l in L])
    rows = M.pivot_rows()
    LieI = symmalg_homo([L[i] for i in rows],n_vars)
    return LieI

    

