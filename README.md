# VMH-RealQuadraticNumberFields
Magma and GAP methods for working with arithmetic groups over real quadratic number fields. These methods are derived from the methods described in the following articles:
* [Perfect lattices over imaginary quadratic number fields](http://de.arxiv.org/abs/1304.0559) (O. Braun and R. Coulangeon, Mathematics of Computation, 2015)
* [Computing in arithmetic groups with Voronoi's algorithm](https://arxiv.org/abs/1407.6234) (O. Braun, R. Coulangeon, G. Nebe and S. Schönnenbeck, Journal of Algebra, 2015)
* [Resolutions for unit groups of orders](https://arxiv.org/abs/1609.08835) (S. Schönnenbeck, Journal of Homotopy and related structures, 2016)

The implementation was primarily done by Sebastian Schönnenbeck during his time as doctoral students / postdoc at RWTH Aachen University funded by the DFG Research Training Group "Experimental and constructive algebra" (PhD) and the DFG collaborative research center TRR195 (postdoc). The implementation draws heavily on the analogous algorithms for [imaginary quadratic number fields](https://github.com/schoennenbeck/VMH-ImaginaryQuadraticNumberFields) implemented by Oliver Braun and the author.

Some results of computations performed using these algorithms are already available in our [database](http://www.math.rwth-aachen.de/~Oliver.Braun/unitgroups/). When (not if) you find a bug, feel free to open an issue or try to fix it yourself (good luck reading our code) and open a pull request. For the time being this software is offered as is.

## Overview
The algorithms we implemented deal with groups of the form $GL_n(\mathbb{Z}_K)$ for $n=2,3$ and $K$ a real number field. The following algorithms are available:
* Computing a presentation (i.e. generators and defining relations).
* Solving constructive membership problems (i.e. writing a given element in these generators).
* Computing a contractible G-complex which can be used for homology computations with the GAP-package [HAP](http://hamilton.nuigalway.ie/Hap/www/). 

Most of these algorithms are also available for finite index subgroups of the base group (as long as we know the index and how to check for membership in this group).


## Usage
Overall, the usability of the algorithms is not great and a lot of the general design of the Magma-package is pretty terrible. However, for reasons of me no longer working in academia and generally not wanting to do the refactoring it is going to stay this way for the foresesable future. If you are willing to overlook these weaknesses, performing computations with our packages works as follows: TODO