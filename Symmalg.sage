def rank_poly(M):
    '''
	Input:  Matrix M — entries of "M" are polynomials
	Output: a positive integer -- this is the rank of the matrix M after substituting variables with random rational values. 
    '''
    R=M.base_ring()
    D={}
    for i in range(len(R.gens())):
        D[R.gens()[i]]=QQ.random_element(num_bound=10^3,den_bound=10^3)
    rank1=M.subs(D).rank()

    D={}
    for i in range(len(R.gens())):
        D[R.gens()[i]]=QQ.random_element(num_bound=10^3,den_bound=10^3)
    rank2=M.subs(D).rank()
    return max(rank1,rank2)


def monomial_generator(variables, degree):
    '''
	Input: a list of variables and a positive integer
	Output: all monomials in the given variables whose degree is the provided integer. The monomials are listed in the reverse lexicographic order. 

    Example: monomial_generator( [x, y], 2)= [y^2, x*y, x^2]
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
	Input: a monomial, a matrix g of indeterminate entries, the number n of variables in the ambient polynomial ring. If not provided, it is inferred from the monomial’s parent ring.
	Output: a polynomial which is the Lie derivative of the provided monomial with respect to matrix g of indeterminates. The derivative is computed by applying the transformation `g` to each variable in the monomial and summing over the resulting transformed terms.
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
    Computes the Lie derivative of a polynomial with respect to a given matrix.

    The function calculates the Lie derivative of a polynomial `poly` with respect to 
    a matrix `g`, which represents an infinitesimal transformation. The derivative is 
    computed by applying the Lie derivative operator to each monomial in the polynomial.

    Parameters:
    ----------
    poly : Polynomial
        The polynomial whose Lie derivative is to be computed.
    g : Matrix
        The matrix representing the transformation with respect to which the Lie derivative is calculated.
    n : int, optional (default=0)
        The number of variables in the ambient polynomial ring. If not provided (n=0), 
        it is inferred from the polynomial’s parent ring.

    Returns:
    -------
    der : Polynomial
        The resulting polynomial after applying the Lie derivative.

    Notes:
    ------
    - If `n` is not specified, it is inferred from the polynomial’s ring.
    - The function iterates through each monomial in `poly`, applying the Lie derivative.
    - The final derivative is obtained as a sum over all transformed monomials, weighted by their coefficients.

    Example:
    --------
    Given a polynomial `f = x^2 + xy` and a matrix `g` representing a linear transformation:
    
        g = Matrix([[0, -1], [1, 0]])   # A simple rotation matrix
    
    Calling `lie_derivative_poly(f, g, n=2)` would return the Lie derivative of `f` with respect to `g`.
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
    Converts a polynomial into its vector representation.

    This function takes a polynomial and returns its corresponding vector representation 
    by extracting the coefficients of all monomials up to a specified degree.

    Parameters:
    ----------
    polynomial : Polynomial
        The polynomial to be converted into vector form.
    n : int, optional (default=0)
        The number of variables in the ambient polynomial ring. If not provided (n=0), 
        it is inferred from the polynomial's parent ring.
    degree : int, optional (default=0)
        The degree of the polynomial. If not provided (degree=0), 
        it is inferred from the polynomial itself.

    Returns:
    -------
    vec : list
        A list representing the vectorized form of the polynomial, where each entry corresponds 
        to the coefficient of a monomial in the chosen basis.

    Notes:
    ------
    - If `n` is not specified, the function determines the number of variables from the polynomial's ring.
    - If `degree` is not specified, it is inferred from the polynomial.
    - The function constructs a monomial basis of the given degree and extracts coefficients accordingly.
    - The resulting vector has length equal to the number of monomials of degree `d` in `n` variables, 
      computed as `binomial(n + d - 1, d)`.

    Example:
    --------
    Given a polynomial in 3 variables:
    
        f = x^2 + 2xy + 3y^2 + xz
    
    Calling `poly_to_vec(f, n=3, degree=2)` would return a vector of coefficients 
    corresponding to the monomial ordering.

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
    Computes the symmetry Lie algebra of a homogeneous prime ideal.

    This function takes generators of a **homogeneous prime ideal** and computes the symmetry Lie algebra
    of the ideal. It assumes that all the generating polynomials are **homogeneous** and have the **same degree**.

    Parameters:
    ----------
    generators : list
        A list of polynomial generators defining the homogeneous prime ideal.
    n : int, optional (default=0)
        The number of variables in the ambient polynomial ring. If not provided (n=0), 
        it is inferred from the first generator.

    Returns:
    -------
    LieI : GAP Lie Algebra object
        The computed symmetry Lie algebra represented as a GAP Lie Algebra.

    Notes:
    ------
    - Constructs a polynomial ring with variables for both original polynomial variables and matrix coefficients.
    - Computes the Lie derivatives of the generators using a symbolic matrix representation.
    - Forms a system of equations from minors of matrices to determine symmetry constraints.
    - Computes the kernel of the coefficient matrix to obtain basis elements of the Lie algebra.
    - Uses GAP to define the resulting Lie algebra.

    Output:
    -------
    - Displays a basis of the computed Lie algebra as a list of matrices.
    
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
    Computes the symmetry Lie algebra of an ideal generated by the given polynomials.
    
    This function takes a list of polynomial generators defining an ideal and computes its symmetry Lie algebra.
    It constructs a polynomial ring, determines an appropriate basis, and applies a homomorphism to obtain the 
    symmetry Lie algebra.

    Parameters:
    ----------
    generators : list
        A list of polynomial generators defining the ideal.
    n : int, optional (default=0)
        The number of variables in the ambient polynomial ring. If not specified (n=0), 
        it is inferred from the first generator.

    Returns:
    -------
    LieI : Lie algebra object
        The computed symmetry Lie algebra of the given ideal.

    Notes:
    ------
    - If `n` is not provided, the number of variables is inferred from the first generator.
    - Constructs a polynomial ring over the rationals.
    - Expands the generators into a basis by multiplying with monomials of appropriate degree.
    - Uses row reduction on the matrix representation of the expanded generators.
    - Calls `symmalg_homo` to finalize the Lie algebra structure.
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
