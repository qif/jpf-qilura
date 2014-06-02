QILURA
======
__Q__uantify __I__nformation __L__eaks __U__sing __R__eliability __A__nalysis

Description
-----------
A tool for qualitative and quantitative information flow analysis using [Symbolic PathFinder](http://babelfish.arc.nasa.gov/trac/jpf/wiki/projects/jpf-symbc).

Install
-------
QILURA requires the following tools to be installed: [Symbolic PathFinder](http://babelfish.arc.nasa.gov/trac/jpf/wiki/projects/jpf-symbc), [z3 for Java](http://leodemoura.github.io/blog/2012/12/10/z3-for-java.html), [Omega](https://github.com/davewathaverford/the-omega-project) and [Latte](https://www.math.ucdavis.edu/~latte/).

In the root folder of the JPF toolsets, edit the `site.properties` file as follows:

        jpf-home = /homes/qsp30/Programs/jpf # change this with your directory
        jpf-core = ${jpf-home}/jpf-core 
        jpf-symbc = ${jpf-home}/jpf-symbc
        jpf-qilura = ${jpf-home}/jpf-qilura
        extensions+=,${jpf-core} 
        extensions+=,${jpf-symbc}
        extensions+=,${jpf-qilura} 
        
Download __jpf-qilura__ from the github repository, then run:  

        ant build

And that's it. There are a set of small case studies under `jpf-qilura/src/examples`. The python script `configEx.py` automatically fixes the configurations for the examples corresponding to your installation of Omega and Latte.

All the examples are set for quantitative information flow analysis. Except for `SanityCheck1`, which sets `symbolic.sif.analysis=qualitative` for qualitative analysis.


