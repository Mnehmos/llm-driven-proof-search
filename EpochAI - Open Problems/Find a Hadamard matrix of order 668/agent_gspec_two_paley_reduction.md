# Two-Paley reduction for cyclic GS(167)

Take the valid GS row-sum fibre `(21,15,1,1)`, since
`21^2 + 15^2 + 1^2 + 1^2 = 668`.  Fix each row-sum-one sequence to the
Paley sequence on `Z_167`, whose periodic autocorrelation is `-1` at every
nonzero shift.  The two remaining binary sequences `A,B` must therefore obey

`PAF_A(d) + PAF_B(d) = 2` for every `d=1,...,83`.

If `X,Y` are their `-1` supports, then `|X|=73`, `|Y|=76`, and the condition
is exactly the cyclic supplementary-difference-set parameter set
`(167;73,76;66)`.  Equivalently, the two sequences have 166 total cyclic
disagreements at every nonzero shift and Fourier power sum 332 at every
nonzero frequency.  Any solution, together with the two Paley rows, is a
cyclic Goethals--Seidel input of order 167 and hence yields a Hadamard matrix
of order 668.

The parameter set is explicitly marked unknown (`?`) in Table 1 of Dragomir
Z. Djokovic and Ilias S. Kotsireas, *New results on D-optimal matrices*,
Journal of Combinatorial Designs 20(6), 278--289 (2012), arXiv:1103.3626:
https://arxiv.org/abs/1103.3626

Thus this reduction identifies a recognized open cyclic D-optimal-design
subproblem; it does not import an existing witness.
