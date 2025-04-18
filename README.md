# Toric via symmetry
This repository hosts an implementation of an algorithm for computing the symmetry Lie algebra of an ideal, given its generators, based on the preprint [Symmetry Lie Algebras of Varieties with Applications to Algebraic Statistics](https://arxiv.org/abs/2309.10741). A version can be found on arXiv:2309.10741. It contains computational details for the examples in this preprint. 

SageMath version 10.3, Release Date: 2024-03-19                   
Using Python 3.11.8.     

The implimentation is in the file `Symmalg.sage` It is based on Theorem 1.2. Note that the algorithm works with $M_i(g)^{transpose}$ instead. 

Details on examples shared in the preprint are found in `Example_5.1.ipynb`,`Example_5.2.ipynb`, `Example_5.5.ipynb', 'Example_5.7', and 'Example_5.10'. 

In `Example_5.2.ipynb`, we compute the symmetry Lie algebra for the vanishing ideal $I$ of the caterpilar tree in one stage of depth and degree 3 in Figure 2 in the paper. This Lie algebra has dimension 2, while the ideal itself has dimension 3. By Theorem 1 in the paper, there is no linear chnge of variables that turns $I$ into a toric ideal. This is the smallest and first **non-toric** one stage tree model. 

Note: 

## Documentation (descriptions of the functions)

`symmalg(generators, n = 0)` 
this is our main function, implemented in `Symmalg.sage`. The input is a set of polynomials in a polynomial ring specified earlier.  It returns the Lie algebra of the ideal generated by these polynomials (GAP Lie object) and it prints out a basis for it. 

    
`rank_poly(M)` 
this function takes a matrix "M" with polynomial entries as input, substitutes random values for the variables, and then returns the rank of the matrix.


### Example

To compute the symmetry Lie algebra of the ideal generated by $x^2+y^2+z^2$ we do: 

```
load('Symmalg.sage')
R = PolynomialRing(QQ,['x', 'y','z']) # initiate the ring
R.inject_variables()  # inject the variables
LieI = symmalg([x^2+y^2+z^2],3) # call the function 
```

If we would like to display computation time, we substitute the last line by:
```
import time
start_time = time.time()
LieI = symmalg([x^2+y^2+z^2],3)
end_time = time.time()
comp_time = end_time - start_time # Compute the elapsed time
minutes = int(comp_time // 60)
seconds = comp_time % 60
formatted_time_str = f"{minutes} min {seconds:.2f} sec"
print(f"\nComputation Time: {formatted_time_str}")
```
All examples throughout the paper run in less than 2.5 minutes, except for the ideal of the caterpillar tree, which is done separately in `ToricIdeal_9x9_conjecture_disproved.ipynb`.


### Computations for symmetry Lie algebra of the caterpillar tree (Example 5.2). 

`Example_5.2.ipynb` is done differently, not just by running the  ```symmalg()``` command. This is because the runing time was high; it was requiring more than 6 hours. The challenge is in solving this very large linear system of $18\binom{45}{19}$ equations: solving for all $19\times 19$ minors of 18 matrices, each of dimensions $19\times 45$. We then decided to intervine and use the specific structure of the ideal. We intervine by 
- for each matrix $M_i(g)$, we remove rows of all zero entries,
- fix variable $g_{kl}$ and a linear equation containing this variable. Solve this equation for $g_{kl}$; that is, write it in the form $g_{kl} = \sum \alpha_{rs} g_{rs}$. Substitute $g_{kl}$ with this sum in each matrix $M_i(g)$. The new system has one less parameter.

We continue with the second procedure of eleminating a variable until all matrices have rank less 19. 

