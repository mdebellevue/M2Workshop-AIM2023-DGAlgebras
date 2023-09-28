needsPackage "DGAlgebras"
DGIdeal = new Type of Ideal
dgIdeal = method(TypicalValue => DGIdeal, Options => true)
dgIdeal (List) := {DifferentiateGens => true} >> o -> S -> (
    I := new  MutableHashTable;
    -- Protect input to avoid side effects
    genList := S;
    I#(symbol natural) = ideal(genList);
    -- The line above already checks that elem of S are in a common ring, so this works
    Anat := ring S#0;
    A := Anat.cache.dgAlgebra;
    -- TODO:
    -- This shouldn't be ring, ring should be R
    I#(symbol ring) = A;
    I#(symbol underlyingAlgebra) = A.natural;
    I#(symbol dgAlgebra) = A;
    if o.DifferentiateGens then (
	    for s in S do (
		ds := diff(A,s);
		if ds % I.natural != 0 then (
		    genList = append(genList,ds);
		    I.natural = ideal(genList);
    	    	);
	    );
	);
    I#(symbol generators) = generators I.natural;
    new DGIdeal from I
    )
-- Accept sensible inputs
    
dgIdeal (RingElement) := {DifferentiateGens => true} >> o -> x -> dgIdeal({x}, DifferentiateGens => o.DifferentiateGens)
dgIdeal (Sequence) := {DifferentiateGens => true} >> o -> S -> dgIdeal(toList(S), DifferentiateGens => o.DifferentiateGens)
    
-- Display
-- This may be fixed by making dg algebras rings and dg ideals ideals
net DGIdeal := I -> (
    stack(net I.natural,"DGIdeal of " | toString(I.underlyingAlgebra))
    )
    
-- Overload Various Operations for Ideals
-*
Number % DGIdeal -- see "%" -- a binary operator, usually used for remainder and reduction
DGIdeal * CoherentSheaf -- see "*" -- a binary operator, usually used for multiplication
DGIdeal * Module -- see "*" -- a binary operator, usually used for multiplication
DGIdeal * Vector -- see "*" -- a binary operator, usually used for multiplication
DGIdeal + RingElement -- see "+" -- a unary or binary operator, usually used for addition
DGIdeal == DGIdeal -- see "==" -- equality
DGIdeal == Module -- see "==" -- equality
DGIdeal == DGlgebraRing -- see "==" -- equality
DGIdeal == ZZ -- see "==" -- equality
DGModule == DGIdeal -- see "==" -- equality
Ring == DGIdeal -- see "==" -- equality
ZZ == DGIdeal -- see "==" -- equality
-- We need to think about these carefully
basis(DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(InfiniteNumber,InfiniteNumber,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(InfiniteNumber,List,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(InfiniteNumber,ZZ,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(List,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(List,InfiniteNumber,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(List,List,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(List,ZZ,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(ZZ,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(ZZ,InfiniteNumber,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(ZZ,List,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
basis(ZZ,ZZ,DGIdeal) -- see "basis" -- basis or generating set of all or part of a ring, ideal or module
-- Hard to define, but should use a semifree res and compute ranks over the dga
betti(DGIdeal) -- see "betti" -- display or modify a Betti diagram
comodule(DGIdeal) -- see "comodule" -- submodule to quotient module
quotient(DGIdeal) -- see "comodule" -- submodule to quotient module
degree(DGIdeal)
degrees(DGIdeal) -- see "degrees(Ring)" -- degrees of generators
-* probably not these
euler(DGIdeal) -- Euler characteristic
eulers(DGIdeal) -- list the sectional Euler characteristics
*-
-*
Ext(DGIdeal,DGIdeal) -- see "Ext(Module,Module)" -- total Ext module
Ext(DGIdeal,Module) -- see "Ext(Module,Module)" -- total Ext module
Ext(DGIdeal,Ring) -- see "Ext(Module,Module)" -- total Ext module
Ext(Module,DGIdeal) -- see "Ext(Module,Module)" -- total Ext module
Ext^ZZ(Matrix,DGIdeal) -- see "Ext^ZZ(Matrix,Module)" -- map between Ext modules
Ext^ZZ(DGIdeal,Matrix) -- see "Ext^ZZ(Module,Matrix)" -- map between Ext modules
Ext^ZZ(DGIdeal,DGIdeal) -- see "Ext^ZZ(Module,Module)" -- Ext module
Ext^ZZ(DGIdeal,Module) -- see "Ext^ZZ(Module,Module)" -- Ext module
Ext^ZZ(DGIdeal,Ring) -- see "Ext^ZZ(Module,Module)" -- Ext module
Ext^ZZ(Module,DGIdeal) -- see "Ext^ZZ(Module,Module)" -- Ext module
flattenRing(DGIdeal) -- see "flattenRing" -- write a ring as a (quotient of a) polynomial ring
gb(DGIdeal) -- see "gb" -- compute a Gröbner basis
gbRemove(DGIdeal) -- see "gbRemove" -- remove Gröbner basis
gbSnapshot(DGIdeal) -- see "gbSnapshot" -- the Gröbner basis matrix as so far computed
generator(DGIdeal) -- see "generator" -- provide a single generator
-- Need to think about internal grading also
DGIdeal _ ZZ -- see "generators of ideals and modules"
generators(DGIdeal) -- the generator matrix of an ideal
groebnerBasis(DGIdeal) -- see "groebnerBasis" -- Gröbner basis, as a matrix
hilbertFunction(List,DGIdeal) -- see "hilbertFunction" -- the Hilbert function
hilbertFunction(ZZ,DGIdeal) -- see "hilbertFunction" -- the Hilbert function
Hom(DGIdeal,DGIdeal) -- see "Hom(Module,Module)" -- module of homomorphisms
Hom(DGIdeal,Module) -- see "Hom(Module,Module)" -- module of homomorphisms
Hom(DGIdeal,Ring) -- see "Hom(Module,Module)" -- module of homomorphisms
Hom(Module,DGIdeal) -- see "Hom(Module,Module)" -- module of homomorphisms
Hom(Ring,DGIdeal) -- see "Hom(Module,Module)" -- module of homomorphisms
DGIdeal * ZZ
DGIdeal + Number
DGIdeal / Function -- apply a function to generators of an ideal
DGIdeal / Function -- apply a function to generators of an ideal
DGIdeal / DGIdeal -- quotient module
DGIdeal ^ Array -- bracket power of an ideal
DGIdeal _* -- get the list of generators of an ideal
isHomogeneous(DGIdeal) -- see "isHomogeneous" -- whether something is homogeneous (graded)
-- Should detect when a dgmodule is an ideal
isDGIdeal(DGIdeal) -- see "isDGIdeal" -- whether something is an ideal
isSubset(DGIdeal,DGIdeal) -- whether one object is a subset of another
isSubset(DGIdeal,Module) -- see "isSubset(Module,Module)" -- whether one object is a subset of another
isSubset(Module,DGIdeal) -- see "isSubset(Module,Module)" -- whether one object is a subset of another
-- Maybe
koszulComplexDGA(DGIdeal) -- Returns the Koszul complex as a DGAlgebra
leadTerm(DGIdeal) -- get the ideal of greatest terms
leadTerm(ZZ,DGIdeal) -- get the ideal of lead polynomials
lift(DGIdeal,type of QQ) -- see "lift" -- lift to another ring
lift(DGIdeal,type of ZZ) -- see "lift" -- lift to another ring
Matrix % DGIdeal -- see "methods for normal forms and remainder" -- normal form of ring elements and matrices
RingElement % DGIdeal -- see "methods for normal forms and remainder" -- normal form of ring elements and matrices
mingens(DGIdeal) -- see "mingens(Module)" -- minimal generator matrix
minimalBetti(DGIdeal) -- see "minimalBetti" -- minimal betti numbers of (the minimal free resolution of) a homogeneous ideal or module
Module / DGIdeal -- see "Module / Module" -- quotient module
DGIdeal _ List -- see "Module _ List" -- map from free module to some generators
module(DGIdeal)
multidegree(DGIdeal) -- see "multidegree" -- multidegree
multiplicity(DGIdeal) -- see "multiplicity" -- Compute the Hilbert-Samuel multiplicity of an ideal
multiplicity(DGIdeal,RingElement) -- see "multiplicity" -- Compute the Hilbert-Samuel multiplicity of an ideal
Number + DGIdeal
numgens(DGIdeal) -- number of generators of an ideal
poincare(DGIdeal) -- see "poincare" -- assemble degrees of a ring, module, or ideal into a polynomial
preimage(RingMap,DGIdeal) -- see "preimage" -- preimage of an ideal under a ring map
Module : DGIdeal -- see "quotient(Module,Module)" -- ideal or submodule quotient
quotient(Module,DGIdeal) -- see "quotient(Module,Module)" -- ideal or submodule quotient
random(List,DGIdeal) -- see "random(ZZ,DGIdeal)" -- get a random homogeneous element from a graded ideal
random(ZZ,DGIdeal) -- get a random homogeneous element from a graded ideal
regularity(DGIdeal) -- see "regularity" -- compute the Castelnuovo-Mumford regularity
resolution(DGIdeal) -- compute a projective resolution of (the quotient ring corresponding to) an ideal
ring(DGIdeal) -- see "ring" -- get the associated ring of an object
Ring / DGIdeal -- make a quotient ring
RingElement + DGIdeal
saturate(Module,DGIdeal) -- see "saturate" -- saturation of ideal or submodule
saturate(Vector,DGIdeal) -- see "saturate" -- saturation of ideal or submodule
singularLocus(DGIdeal) -- see "singularLocus" -- singular locus
specialFiber(DGIdeal) -- see "specialFiber" -- Special fiber of a blowup
specialFiber(DGIdeal,RingElement) -- see "specialFiber" -- Special fiber of a blowup
substitute(DGIdeal,Option) -- see "substitute" -- substituting values for variables
support(DGIdeal) -- list of variables occurring in the generators of an ideal
toDual(ZZ,DGIdeal) -- see "toDual" -- finds the inverse system to an ideal up to a given degree
Tor_ZZ(DGIdeal,Matrix)
Tor_ZZ(Matrix,DGIdeal)
Tor_ZZ(DGIdeal,DGIdeal) -- see "Tor_ZZ(Module,Module)" -- compute a Tor module
Tor_ZZ(DGIdeal,Module) -- see "Tor_ZZ(Module,Module)" -- compute a Tor module
Tor_ZZ(DGIdeal,Ring) -- see "Tor_ZZ(Module,Module)" -- compute a Tor module
Tor_ZZ(Module,DGIdeal) -- see "Tor_ZZ(Module,Module)" -- compute a Tor module
Vector % DGIdeal
versalEmbedding(DGIdeal) -- see "versalEmbedding" -- Compute a versal embedding
whichGm(DGIdeal) -- see "whichGm" -- Largest Gm satisfied by an ideal
*-

    
isWellDefined DGIdeal := I -> (
    -- If the generators of the ideal are closed under the differential,
    -- Then so is all of I by the Leibniz Rule
    genlist := flatten entries gens J1;
    Idiff = ideal(for gen in genlist list diff(I#dgAlgebra,gen));
    assert Idiff/I==0
    )
    
QuotientDGAlgebra = new Type of MutableHashTable
quotientDGAlgebra = method(TypicalValue => QuotientDGAlgebra)
quotientDGAlgebra (DGAlgebra,DGIdeal) := (A,I) -> (
    Q = new MutableHashTable;
    Q#(symbol ring) = A#ring;
    Q#(symbol natural) = A#natural / I#natural;
    Q.natural.cache = new CacheTable;
    Q.natural.cache#(symbol dgAlgebra) = Q
    )
    
    
 
   

