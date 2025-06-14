def rank_poly(M):
    '''
    Compute the rank of a matrix of polynomials after substituting variables with random values.
    Input:
    - M: A matrix whose entries are polynomials from a pre-given polynomial ring R.
    Output:
    - A positive integer representing the rank of the matrix M after substituting variables with random values.
    '''
    R = M.base_ring()
    D = {}
    for i in range(len(R.gens())):
        D[R.gens()[i]] = QQ.random_element(num_bound=10**3, den_bound=10**3)
    rank1 = M.subs(D).rank()
    D = {}
    for i in range(len(R.gens())):
        D[R.gens()[i]] = QQ.random_element(num_bound=10**3, den_bound=10**3)
    rank2 = M.subs(D).rank()
    return max(rank1, rank2)


def monomial_generator(variables, degree):
    '''
    Generate all monomials in the given variables and degree.
    Input:
    - variables: A list of variables.
    - degree: A positive integer representing the degree of the monomials.
    Output:
    - A list of all monomials in the given variables and degree, presented in the reverse lexicographic order.
    '''
    n_vars = len(variables)
    degs = list(WeightedIntegerVectors(degree, [1 for i in range(n_vars)]))
    monomials = []
    for d in degs:
        mon = 1
        for i in range(n_vars):
            mon *= variables[i]**d[i]
        monomials.append(mon)
    return monomials


def lie_derivative_mono(monomial, g, n=0):
    '''
    Compute the Lie derivative of a monomial with respect to a given transformation matrix.
    Input:
    - monomial: A single-term polynomial whose Lie derivative is to be computed.
    - g: A matrix representing the infinitesimal transformation.
    - n: The number of variables in the ambient polynomial ring (optional, default=0).
    Output:
    - The resulting polynomial after applying the Lie derivative.
    '''
    if n == 0:
        n_vars = len(monomial.parent().gens())
    else:
        n_vars = n
    R = monomial.parent()
    X = matrix(R, n_vars, 1, R.gens()[:n_vars])
    gen_index = {R.gens()[l]: l for l in range(len(R.gens()))}
    der = 0
    for x in monomial.factor():
        l = (g[gen_index[x[0]], :] * X)[0, 0]
        der += l * R(monomial / x[0]) * x[1]
    return der


def lie_derivative_poly(poly, g, n=0):
    '''
    Compute the Lie derivative of a polynomial with respect to a given transformation matrix.
    Input:
    - poly: The polynomial whose Lie derivative is to be computed.
    - g: A matrix representing the infinitesimal transformation.
    - n: The number of variables in the ambient polynomial ring (optional, default=0).
    Output:
    - The resulting polynomial after applying the Lie derivative.
    '''
    if n == 0:
        n_vars = len(poly.parent().gens())
    else:
        n_vars = n
    der = 0
    for mon, coef in zip(poly.monomials(), poly.coefficients()):
        der += lie_derivative_mono(mon, g, n_vars) * coef
    return der


def poly_to_vec(polynomial, n=0, degree=0):
    '''
    Convert a homogeneous polynomial into its vector representation based on a monomial basis.
    Input:
    - polynomial: The polynomial to be converted into a vector.
    - n: The number of variables in the ambient polynomial ring (optional, default=0).
    - degree: The degree of the polynomial (optional, default=0).
    Output:
    - A list representing the vectorized form of the polynomial, where each entry corresponds to the coefficient of a monomial in the chosen basis.
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
    n_2 = binomial(n_vars + d - 1, d)
    monomials = monomial_generator(R.gens()[:n_vars], d)
    vec = [0] * n_2
    for i in range(n_2):
        vec[i] = polynomial.coefficient(monomials[i])
    return vec


def symmalg_homo(generators, n=0):
    '''
    Compute the symmetry Lie algebra of a homogeneous prime ideal.
    Input:
    - generators: A list of polynomial generators defining the homogeneous prime ideal. All generators must be homogeneous polynomials of the same degree.
    - n: The number of variables in the ambient polynomial ring (optional, default=0).
    Output:
    - LieI: The computed symmetry Lie algebra represented as a GAP Lie Algebra object.
    '''
    S = generators[0].parent()
    if n != 0:
        n_vars = n
    else:
        n_vars = len(S.gens())
    var = [str(t) for t in S.gens()[:n_vars]]
    var += ['g%i%i' % (i, j) for i in range(1, n_vars + 1) for j in range(1, n_vars + 1)]
    R = PolynomialRing(QQ, var)
    R.inject_variables()
    gens = [R(g) for g in generators]
    d = gens[0].degree()
    g = matrix(R, n_vars, n_vars, R.gens()[n_vars:])
    gens_vecs = [poly_to_vec(gen, n_vars) for gen in gens]
    der_gens_vecs = [poly_to_vec(lie_derivative_poly(gen, g, n_vars), n_vars, d) for gen in gens]
    matrices = [matrix(gens_vecs + [i]) for i in der_gens_vecs]
    eqns = set()
    for M in matrices:
        for eqn in M.minors(len(gens) + 1):
            if eqn != 0:
                eqns.add(eqn)
    eqns = list(eqns)
    ker = []
    for eqn in eqns:
        l = [eqn.coefficient(gij) for gij in R.gens()[n_vars:]]
        ker.append(l)
    K = matrix(ker)
    rows = K.pivot_rows()
    K = K[rows, :]
    K_ker = K.right_kernel_matrix()
    L = [matrix(QQ, n_vars, n_vars, r) for r in K_ker.rows()]
    LieI = gap.LieAlgebra(gap.Rationals, L)
    print('\nA basis of the Lie algebra consists of the following matrices:\n')
    show(L)
    return LieI


def symmalg(generators, n=0):
    '''
    Compute the symmetry Lie algebra of a homogeneous ideal generated by the given polynomials.
    Input:
    - generators: A list of polynomial generators defining the ideal.
    - n: The number of variables in the ambient polynomial ring (optional, default=0).
    Output:
    - LieI: The computed symmetry Lie algebra of the given ideal.
    '''
    S = generators[0].parent()
    if n != 0:
        n_vars = n
    else:
        n_vars = len(S.gens())
    var = [str(t) for t in S.gens()[:n_vars]]
    R = PolynomialRing(QQ, var)
    R.inject_variables()
    gens = [R(g) for g in generators]
    d = max([g.degree() for g in gens])
    L = []
    for g in gens:
        monomials = monomial_generator(R.gens()[:n_vars], d - g.degree())
        for m in monomials:
            L.append(g * m)
    M = matrix(R, [poly_to_vec(l, n_vars, d) for l in L])
    rows = M.pivot_rows()
    LieI = symmalg_homo([L[i] for i in rows], n_vars)
    return LieI
