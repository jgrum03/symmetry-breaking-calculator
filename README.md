# Symmetry Breaking Calculator
This is a calculator using GAP which determines the broken algebra and can brush through sweeps of algebras.

The document [adjointCentralizerCalculator.g](adjointCentralizerCalculator.g) can sweep through all nilpotent vevs in the adjoint rep for a given algebra. It does this by knowing all the nilpotent orbits of the algebra, then going systematically through each orbit, finding an example nilpotent, then doing the breaking procedure.

The document [centralizerCaluclator.g](centralizerCalculator.g) was my original first attempt. With that document, you can choose any representation, not just the adjoint, and it will spit out what it breaks to.

## Instructions To Use [adjointCentralizerCalculator.g](adjointCentralizerCalculator.g):
At the top of the doc, there is a variable titled `algebra`, in a line of the form
```
algebra := ["A",2];;
```
Simply change this list to whatever algebra you would like, and it will start spitting out all possible breaking patterns.

## Instructions To Use [centralizerCalculator.g](centralizerCalculator.g):
At the top of the doc, there is a block of code which looks like
```
algebra := ["A", 2];;
highestWeight := [1,1];;
stabilizedVectorLabel := [0,0,0,-1,2,0,0,0];;
```
Simply change `algebra` to the algebra you would like to analyze, `highestWeight` to the highest weight vector in the representation you want to analyze, and `stabilizedVectorLabel` to the vector you want to stabilize.

**Note:** The basis for the vector space the algebra acts on is whatever GAP thinks is nice. I might make an option to spit out what the vector you chose looks like in certain nice representations, but this is not implemented yet.
