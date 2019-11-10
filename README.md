# VMH-RealQuadraticNumberFields
Magma and GAP methods for working with arithmetic groups over totally real number fields. These methods are derived from the methods described in the following articles:
* [Perfect lattices over imaginary quadratic number fields](http://de.arxiv.org/abs/1304.0559) (O. Braun and R. Coulangeon, Mathematics of Computation, 2015)
* [Computing in arithmetic groups with Voronoi's algorithm](https://arxiv.org/abs/1407.6234) (O. Braun, R. Coulangeon, G. Nebe and S. Schönnenbeck, Journal of Algebra, 2015)
* [Resolutions for unit groups of orders](https://arxiv.org/abs/1609.08835) (S. Schönnenbeck, Journal of Homotopy and related structures, 2016)

The implementation was primarily done by Sebastian Schönnenbeck during his time as doctoral students / postdoc at RWTH Aachen University funded by the DFG Research Training Group "Experimental and constructive algebra" (PhD) and the DFG collaborative research center TRR195 (postdoc). The implementation draws heavily on the analogous algorithms for [imaginary quadratic number fields](https://github.com/schoennenbeck/VMH-ImaginaryQuadraticNumberFields) implemented by Oliver Braun and the author.

Some results of computations performed using these algorithms are already available in our [database](http://www.math.rwth-aachen.de/~Oliver.Braun/unitgroups/). When (not if) you find a bug, feel free to open an issue or try to fix it yourself (good luck reading our code) and open a pull request. For the time being this software is offered as is.

## Overview
The algorithms we implemented deal with groups of the form $GL_n(\mathbb{Z}_K)$ for $n \geq 2$ and $K$ a totally real number field. In particular the algorithms work for real quadratic number fields, but also for the totally real subfields of cyclotomic fields or for the rationals itself (though there are much better algorithms available in the latter case). However, since the complexity of the computations grows rather quickly with $n$ and (experimentally) with the discriminant of $K$ the algorithms are only really usefull in a relatively narrow window of parameters.

The following algorithms are available:
* Computing a presentation (i.e. generators and defining relations).
* Solving constructive membership problems (i.e. writing a given element in these generators).
* Computing a contractible G-complex which can be used for homology computations with the GAP-package [HAP](http://hamilton.nuigalway.ie/Hap/www/). 

Most of these algorithms are also available for finite index subgroups of the base group (as long as we know the index and how to check for membership in this group).


## Usage
Overall, the usability of the algorithms is not great and a lot of the general design of the Magma-package is pretty terrible. However, for reasons of me no longer working in academia and generally not wanting to do the refactoring it is going to stay this way for the foresesable future. If you are willing to overlook these weaknesses, performing computations with our packages works as follows: 

### General Setup
1. Choose the dimension $n$ (let's say $2$ since basically only $2$ and $3$ are actually feasible) and the (totally real) number field $K$ (let's say $K = \mathbb{Q}(\sqrt{10})$). We will need to edit the file BasicData.m to make this known to Magma. There are four values that need to be set in this file. However, you will not need to touch the last two as long as you want to work with the general linear group (over the integers of $K$) and its finite index subgroups  Edit the file BasicData.m so that it reads:

        QuadraticField(10);
        n:=2;
        V:=KMatrixSpace(K,n,1);
        L:=[IntegralBasis(K)[i]*V.j: i in [1..Degree(K)],j in [1..n]];

You can exchange the value of L for any $\mathbb{Z}$-basis of the n-dimensional K-space V to work with order fixing the corresponding $\mathbb{Z}$-lattice instead. I do not expect anybody actually needs this option, but it's there... 

2. Open Magma and initialize the basic setup by calling:

        AttachSpec("path/to/files/VMH-spec");
        V := VoronoiAlgorithm()
        
### Computing a presentation
If we already have the basic setup from above, computing a presentation works as follows:

        G,g := Presentation(V)

Now G is a finitely presented group and g a homomorphism from G to the matrix group we are interested in. There are a couple of keyword arguments to this command:
* simplify (default: true)  specifies whether Magma should try to simplify the presentation before returning it.
* projective (default: false)  specifies whether you want to compute the quotient modulo -1 instead of the matrix group
* CheckMembership (default: 0). Here you can provide a function checking an element of the full matrix group for membership in a (finite index) subgroup. If you do a presentation of this subgroup is computed instead of a presentation for the full group.

### Solving constructive membership problems
We suppose we already have the presentation from the last step (if not it is actually computed when you first try to solve an constructive membership problem). Given an element $M \in \GL_n(\mathbb{Z}_K)$ we now want to find $m \in G$ such that $g(m) = M$.
To do this call:

        m := SolveWordProblem(M, V)
        
### Constructing a contractible G-complex
This workflow is a little messier and requires us to write things to a text-file which will later be used by GAP. We again assume that we already have the general setup ready.
1. If we want to work with the full group, i.e. $\GL_n(\mathbb{Z}_K)$ simply call:

        ComputeComplexGL("path/to/store/filename", V)
2. If we want to work with a finite index subgroup. We need a function checking for membership in this subgroup. For example if we have an ideal I and want the subgroup of matrices whose lower left entry is in I we could define:

        CheckMembership := func<x| IsInGL(x) and x[2][1] in I>;
3. Moreover we need the index of this subgroup in the full group (this is usually known to us) and a system of right-coset-representatives of the subgroup in the full group. You can either choose to provide your own favorite system of representatives or call the following command (note that this will run forever if the index you provide is larger than the actual index):

        Reps:=SystemOfRepresentativesFiniteIndex(V`MultFreeList,CheckMembership,index);
        
4. Now constructing the file can be done by calling:

        ComputeComplexLowIndexSubgroup("path/to/store/filename", Reps, CheckMembership , V);
        
**Now we switch over to GAP.**

1. To get the necessary functionalities call (ignore all warnings, I tried to get rid of them at some point but just could not be bothered):

        LoadPackage("HAP");
        Read("path/to/gapstuff/ReadWellRoundedComplex.gi");
        
2. To get the contractible G-complex (non-free G-resolution) up to dimension 'length' (can be arbitrarily high without actually hurting performance) we constructed in Magma call:

        R := ResolutionFromWellRoundedComplex(file, length);
        
3. This gives you a non-free G-resolution in HAP which you can work with in the usual way. For instance you could compute a free resolution (of the integers) by calling

        F := FreeGResolution(R, length);
        
4. We provide two more GAP-functionalities. In the file 'QuotientComplex.gi' we define a function QuotientComplex which takes in a contractible G-complex and a central subgroup of G acting trivially on the complex and outputs a contractible complex for the quotient group. Moreover, the file 'WriteComplex.gi' defines a function WriteComplex taking in a contractible G-complex and a filename and stores the contractible G-complex in HAP-readable format in the file (eliminating the need to use our GAP-functionalities when sharing complexes with other people).

## Additional comments
1. Why the hell can I not use Latex in the ReadMe?
2. License: No clue. If you use these algorithms for your research please cite the corresponding papers. If you use these algorithms for commercial purposes please let me know, I will be mightily impressed that you found a real world use-case...
3. In case you were wondering: VMH stands for Voronoi, Minimal Classes, and Homology.
