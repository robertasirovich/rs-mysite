newPackage("ConstantRankMatrices",
     Version => "1.1", 
     Date => "January 25, 2017",
     Authors => {
                          {Name => "Ada Boralevi", Email => "ada.boralevi@polito.it"},
                          {Name => "Daniele Faenzi", Email => "daniele.faenzi@u-bourgogne.fr"},
                          {Name => "Paolo Lella", Email => "paolo.lella.math@gmail.com"}
                         },
     Headline => "Ancillary file to the paper \"Truncated modules and linear presentations of vector bundles\""
     )
     
export {
   -- METHODS
   "HorrocksMumfordBundle",
   "TangoBundle",
   "nullCorrelationBundle",
   "generalizedNullCorrelationBundle",
   "tHooftInstantonBundle",
   "specialInstantonBundle",
   "ellipticInstantonBundle",
   "instantonBundle",
   "generalizedSteinerBundle",
   "bettiNumbersLinearResolution",
   "bettiTableLinearResolution",
   "admissibleArtinianPureResolutions",
   "admissibleArtinianPureDegrees",
   "admissibleArtinianPureDegreesLinear",
   "corank2AntiSymmetricMatrix",
   "corank1WestwickMatrix",
   "constantRankMatrix",
   -- OPTIONS
   "Display",
   "CheckingLevel"
  }

needsPackage("BoijSoederberg")
needsPackage("BGG")

----------------------------------------------------------------------------------------------------
----------          HORROCKS-MUMFORD BUNDLE                                               ----------
----------------------------------------------------------------------------------------------------
HorrocksMumfordBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

HorrocksMumfordBundle PolynomialRing := opts -> S -> (
    
    if numgens(S) != 5 then error "coordinate ring of P^4 needed";
	   
    e := local e;
    E := coefficientRing(S)[e_0..e_4, SkewCommutative=>true];
    alphad := map(E^5,E^{2:-2},{{e_4*e_1,e_2*e_3},{e_0*e_2,e_3*e_4},{e_1*e_3,e_4*e_0},{e_2*e_4,e_0*e_1},{e_3*e_0,e_1*e_2}});
    alpha := syz alphad;
    alphad' := beilinson(alphad,S);
    alpha' := beilinson(alpha,S);
    
    return dual dual sheaf prune homology(alphad',alpha');
)

HorrocksMumfordBundle Nothing := opts -> null -> (
        
    x := local x;
    S := (opts.CoefficientRing)[x_0..x_4];
    
    return HorrocksMumfordBundle S;
)

----------------------------------------------------------------------------------------------------
----------          TANGO BUNDLE                                                          ----------
----------------------------------------------------------------------------------------------------
TangoBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

TangoBundle ZZ := opts -> n -> (
    if (n < 2) then error "at least 3 variables expected";
    
    KK := opts.CoefficientRing;
    x := local x;
    S := KK[x_0..x_n];
    return TangoBundle S;
)

TangoBundle PolynomialRing := opts -> S -> (
    if numgens(S) < 4 then error "at least 5 variables expected";
    
    Omega := cotangentSheaf(Proj S);
    T2 := dual exteriorPower(2,Omega);
    H := Hom(S^{2},module T2);
    f := basis(0,H);    
    rand := for i from 0 to rank H - numgens S + 1 list homomorphism(f*random(S^{numColumns f:2}, S^{1:2}));
    MM := matrix ({rand});
    return dual dual sheaf cokernel MM;
)

----------------------------------------------------------------------------------------------------
----------          NULL-CORRELATION BUNDLE                                               ----------
----------------------------------------------------------------------------------------------------
nullCorrelationBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

nullCorrelationBundle ZZ := opts -> n -> (
    if n < 1 then error "positive number of variables expected";
    if n%2 != 1 then error "odd dimension of projective space expected";
    
    x := local x;
    S := (opts.CoefficientRing)[x_0..x_n];

    return nullCorrelationBundle S;
)

nullCorrelationBundle PolynomialRing := opts -> S -> (
    n := numgens S-1;
    if n < 1 then error "positive number of variables expected";
    if n%2 != 1 then error "odd dimension of projective space expected";
    
    Tm1 := (tangentSheaf(Proj S))(-1);
    H := Hom(module Tm1,S^{1});
    f := basis(0,H);
    g := homomorphism (f*random(S^{numColumns f:1},S^{1:1}));
    
    return dual dual sheaf kernel g;
)

----------------------------------------------------------------------------------------------------
----------          GENERALIZED NULL-CORRELATION BUNDLE                                   ----------
----------------------------------------------------------------------------------------------------
generalizedNullCorrelationBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

generalizedNullCorrelationBundle (ZZ,ZZ,ZZ) := opts -> (a,b,c) -> (
   
    x := local x;
    S := (opts.CoefficientRing)[x_0..x_3];

    return generalizedNullCorrelationBundle(S,a,b,c);
)

generalizedNullCorrelationBundle (PolynomialRing,ZZ,ZZ,ZZ) := opts -> (S,a,b,c) -> (

   if numgens S != 4 then error "4 variables expected";
   if b >= c then error "the second integer has to be smaller than the third one";
   if a > b then error "the first integer has to be smaller than or equal to the second one";
   if a < 0 then error "the first integer has to be non-negative";
   
   psi := random(S^{c},S^{b,a,-a,-b});
   syzDegreeC := super basis(c,ker psi);
   phi := syzDegreeC*random(S^{numColumns syzDegreeC:-c},S^{1:-c});
    
   return dual dual sheaf (ker psi/image phi);
)

----------------------------------------------------------------------------------------------------
----------          T'HOOFT INSTANTON BUNDLE                                              ----------
----------------------------------------------------------------------------------------------------
tHooftInstantonBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

tHooftInstantonBundle (PolynomialRing,ZZ) := opts -> (R,k) -> (
  
  if (numgens R)%2 != 0 then error "even number of variables expected";
  if k < 1 then error "positive input expected";
  
  n := (numgens R)//2 - 1; 
  C := random(R^{k:0},R^{n:0});
  mat1 := matrix for i from 1 to k list for j from 1 to k list if i == j then random(1,R) else 0_R;
  mat2 := matrix for i from 1 to n list for j from 1 to n list if i == j then random(1,R) else 0_R;
  mat3 := matrix for i from 1 to k list for j from 1 to k list if i == j then random(1,R) else 0_R;
  mat4 := matrix for i from 1 to n list for j from 1 to n list if i == j then random(1,R) else 0_R;
  
  A := mat1 | (C*mat2) | mat3 | (C*mat4);
  J := (0|(id_(R^(k+n))))||(-(id_(R^(k+n)))|0);
  B := J*transpose(A);
  
  phi := map(R^{2*k+2*n:0},R^{k:-1},B);  
  psi := map(R^{k:1},R^{2*k+2*n:0},A);  

  return dual dual sheaf (ker psi/image phi);
)

tHooftInstantonBundle (ZZ,ZZ) := opts -> (n,k) -> (
  
  if n < 1 then error "positive number of variables expected";
  x := local x;
  S := (opts.CoefficientRing)[x_0..x_(2*n+1)];

  return tHooftInstantonBundle(S,k);
)

----------------------------------------------------------------------------------------------------
----------          ELLIPTIC INSTANTON BUNDLE                                              ----------
----------------------------------------------------------------------------------------------------
ellipticInstantonBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

ellipticInstantonBundle PolynomialRing := opts -> R -> (
  
   P2 := (coefficientRing(R))[Variables=>3];
   IP := ideal(P2_0,P2_1);
   U := (coefficientRing(R))[Variables=>9];
    ---- del Pezzo surface of degree 8
   BLP := ker map(P2,U,gens truncate(3,IP));
   DP := U/BLP;

   ---- elliptic curve as hyperplane section of del Pezzo surface 
   C := BLP+ideal(random(U^{1},U^{0}));
   RC := U/C;
   ---------- generic projection
   h := transpose random(RC^{4:1},RC^{1:0}); 
   hhh := map(RC,R,h); 
      
   ellipticCurve := ker hhh;

   if dim ellipticCurve != 2 or degree ellipticCurve != 8 or genus ellipticCurve != 1 then error "costruction of a random elliptic curve of degree 8 in P^3 failed";
   
   return dual dual ((sheaf (ker (mingens ellipticCurve)_{0,1,2}))(6));
)

ellipticInstantonBundle Nothing := opts -> null -> (
  
  x := local x;
  S := (opts.CoefficientRing)[x_0..x_3];

  return ellipticInstantonBundle S;
)

----------------------------------------------------------------------------------------------------
----------          SPECIAL INSTANTON BUNDLE                                              ----------
----------------------------------------------------------------------------------------------------
specialInstantonBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

specialInstantonBundle (PolynomialRing,ZZ) := opts -> (R,k) -> (
  
  n := numgens R;
  if n%2 != 0 then error "odd dimension of projective space expected";
  if k < 1 then error "positive input expected";
  a := n//2;
  if k > a then error "second input too large";
     
  A1 := matrix  for i from 1 to k list (for j from 1 to k-i list 0_R) | (for j from 1 to a list R_(a-j)) | (for j from k-i+1 to k-1 list 0_R); 
  A2 := matrix  for i from 1 to k list (for j from 1 to k-i list 0_R) | (for j from 1 to a list -R_(n-j)) | (for j from k-i+1 to k-1 list 0_R); 

  B1 := matrix  for i from 1 to k list (for j from k-i+1 to k-1 list 0_R) | (for j from a to n-1 list R_j) | (for j from 1 to k-i list 0_R);   
  B2 := matrix  for i from 1 to k list (for j from k-i+1 to k-1 list 0_R) | (for j from 0 to a-1 list R_j) | (for j from 1 to k-i list 0_R); 
  
  A := A1|A2;
  B := transpose (B1|B2);
  phi := map(R^{n+2*k-2:0},R^{k:-1},transpose A);
  psi := map(R^{k:1},R^{n+2*k-2:0},transpose B);
  
  return dual dual sheaf (ker psi/image phi);     
)

specialInstantonBundle (ZZ,ZZ) := opts -> (n,k) -> (
  if n < 1 then error "positive number of variables expected";
  
  x := local x;
  S := (opts.CoefficientRing)[x_0..x_(2*n+1)];

  return specialInstantonBundle(S,k);
)

----------------------------------------------------------------------------------------------------
----------          GENERALIZED INSTANTON BUNDLE                                          ----------
----------------------------------------------------------------------------------------------------
instantonBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

instantonBundle (ZZ,ZZ,ZZ) := opts -> (n,r,k) -> (
   if n < 1 then error "positive number of variables expected";
   if n%2 == 1 and r < n-1 then error "rank at least equal to the number of variables minus 2 expected";
   if n%2 == 0 and r < n then error "rank at least equal to the number of variables minus 1 expected";
   x := local x;
   S := (opts.CoefficientRing)[x_0..x_n];

   return instantonBundle(S,r,k);
)

instantonBundle (PolynomialRing,ZZ,ZZ) := opts -> (S,r,k) -> (
   n := numgens S - 1;
   if n < 1 then error "positive number of variables expected";
   if r < 1 then error "positive rank of the vector bundle expected";
   if k < 1 then error "positive rank expected";
   if n%2 == 1 and r < n-1 then error "rank at least equal to the number of variables minus 2 expected";
   if n%2 == 0 and r < n then error "rank at least equal to the number of variables minus 1 expected";
   
    B := S^{2*k+r:0};
    C := S^{k:1};
    psi := random(C,B);
    A := super basis (1,ker psi);
    if rank A < k then error "wrong choice of (n,r,k)";
    phi := A*random(S^{numColumns A:-1},S^{k:-1});   

    return dual dual sheaf (ker psi/image phi);
)

----------------------------------------------------------------------------------------------------
----------          STEINER BUNDLE                                            ----------
----------------------------------------------------------------------------------------------------
SteinerBundle = method(TypicalValue => CoherentSheaf,Options=>{CoefficientRing=>ZZ/10007})

SteinerBundle (ZZ,ZZ,ZZ,ZZ) := opts -> (n,r,s,m) -> (
   if n < 1 then error "positive number of variables expected";
   
   x := local x;
   S := (opts.CoefficientRing)[x_0..x_n];

   return SteinerBundle(S,r,s,m);
)

SteinerBundle (PolynomialRing,ZZ,ZZ,ZZ) := opts -> (S,r,s,m) -> (
   n := numgens S;
   if n < 1 then error "positive number of variables expected";
   if r < n-1 then error "rank greater than or equal to the number of variables expected";
   if s < 1 then error "positive rank expected";
   if m < 0 then error "non-negative morphism degree expected";
    
   return dual dual sheaf cokernel random(S^{s+r:0},S^{s:-m-1});
)

generatingBettiFunction = method (TypicalValue => RingElement)
generatingBettiFunction (ZZ,ZZ,PolynomialRing,ZZ) := (n,i,P,j) -> (
    return binomial(n,i)*product(for t from 0 to n list if t == i then 1 else P_0-j+t)/n!
) 

bettiNumbersLinearResolution = method (TypicalValue => Sequence)
bettiNumbersLinearResolution Module := M -> (
    R := ring M;
    n := numgens R - 1;
    reg := regularity M;
    Mreg := truncate(reg,M);
    resM := res Mreg;
    beta := for i from 0 to n list rank resM_i;
    P := QQ[local k];
    return (reg,for i from 0 to n list sum(for j from 0 to n list (-1)^j*beta#j*generatingBettiFunction(n,i,P,j)));   
)

bettiTableLinearResolution = method (TypicalValue => BettiTally)
bettiTableLinearResolution (ZZ,List,ZZ) := (r,genFunc,k) -> (

   P := ring (genFunc#0);
   --phi := map(ZZ,P,{k});
   I := ideal(P_0-k); 
   bettiRes := {};
   --for t from 0 to #genFunc-1 do if phi(genFunc#t) != 0 then bettiRes = bettiRes | { (t,{r+k+t},r+k+t) => phi(genFunc#t) };    
   for t from 0 to #genFunc-1 do if lift((genFunc#t)%I,ZZ) != 0 then bettiRes = bettiRes | { (t,{r+k+t},r+k+t) => lift((genFunc#t)%I,ZZ) };    
   
   return new BettiTally from bettiRes;
)

bettiTableLinearResolution (Module,ZZ) := (M,k) -> (

   S := bettiNumbersLinearResolution M;
   return bettiTableLinearResolution (S#0,S#1,k);
)

admissibleArtinianPureResolutions = method (TypicalValue => List)

admissibleArtinianPureResolutions (ZZ,ZZ,BettiTally) := (n,r,bettiNumbers) -> (
    
    return admissibleArtinianPureResolutions(n,r,flatten entries ((matrix bettiNumbers)^{0}));
)

admissibleArtinianPureResolutions (ZZ,ZZ,List) := (n,r,bettiNumbers) -> (
    
    output := {};
    root := for i from 0 to n+1 list i;
    queue := {(root,3)};
    while #queue > 0 do
    (
	current := first queue;
	queue = delete(current,queue);
	currentDegrees := current#0;
	currentIndex := current#1;
	currentPureBetti := makePureBetti (currentDegrees,TableEntries=>RealizationModules);
	currentPureBettiLeastInteger := makePureBetti (currentDegrees);
	q := lift(currentPureBetti#0,ZZ)//(currentPureBettiLeastInteger#0);
	if currentPureBetti#0 < bettiNumbers#0 and currentPureBetti#1 < bettiNumbers#1 then
	(
	    currentPureBettiDiagram := makePureBettiDiagram (currentDegrees);
	    M := minimalPresentation randomSocleModule(currentDegrees,1);
	    if betti res M === q*currentPureBettiDiagram then
	    (
	    	if -currentPureBetti#0+bettiNumbers#0-r <= -currentPureBetti#1+bettiNumbers#1 then
		(
	            output = output | {((currentDegrees,q),(-currentPureBetti#0+bettiNumbers#0,-currentPureBetti#1+bettiNumbers#1))};  
		);
	    
	        k := 2;
	        while k*currentPureBetti#0 < bettiNumbers#0 and k*currentPureBetti#1 < bettiNumbers#1 do
	        (
		    if -k*currentPureBetti#0+bettiNumbers#0-r <= -k*currentPureBetti#1+bettiNumbers#1 then
		    (
	    	      	output = output | {((currentDegrees,q*k),(-k*currentPureBetti#0+bettiNumbers#0,-k*currentPureBetti#1+bettiNumbers#1))}; 
		    ); 
	     	    k = k+1;
	    	);
	    );
	
	    for i from currentIndex to n+1 do
	    (
	    	newIndices := (for j from 0 to i-1 list currentDegrees#j) | (for j from i to n+1 list currentDegrees#j+1);
		queue = queue | {(newIndices,i)};
	    );
	);
    );
    
    return output;
)

admissibleArtinianPureDegrees = method (TypicalValue => List)

admissibleArtinianPureDegrees (ZZ,ZZ,BettiTally) := (n,r,bettiNumbers) -> (
    
    return admissibleArtinianPureDegrees(n,r,flatten entries ((matrix bettiNumbers)^{0}));
)

admissibleArtinianPureDegrees (ZZ,ZZ,List) := (n,r,bettiNumbers) -> (
    
    output := {};
    root := for i from 0 to n+1 list i;
    queue := {(root,3)};
    while #queue > 0 do
    (
	current := first queue;
	queue = delete(current,queue);
	currentDegrees := current#0;
	currentIndex := current#1;
	currentPureBetti := makePureBetti (currentDegrees,TableEntries=>RealizationModules);
	currentPureBettiLeastInteger := makePureBetti (currentDegrees);
	q := lift(currentPureBetti#0,ZZ)//(currentPureBettiLeastInteger#0);
	if currentPureBetti#0 < bettiNumbers#0 and currentPureBetti#1 < bettiNumbers#1 then
	(
	    --print (currentDegrees,currentPureBetti,currentPureBettiLeastInteger,q);
	    currentPureBettiDiagram := makePureBettiDiagram (currentDegrees);
	    M := minimalPresentation randomSocleModule(currentDegrees,q);
	    if betti res M === q*currentPureBettiDiagram then
	    (   
		if -currentPureBetti#0+bettiNumbers#0-r <= -currentPureBetti#1+bettiNumbers#1 then
		(
		   output = output | {(currentDegrees,q)};  
		);
	    	
	    );
	
	    for i from currentIndex to n+1 do
	    (
	    	newIndices := (for j from 0 to i-1 list currentDegrees#j) | (for j from i to n+1 list currentDegrees#j+1);
		queue = queue | {(newIndices,i)};
	    );
	);
    );
    
    return output;
)

admissibleArtinianPureDegreesLinear = method(TypicalValue=>List)

admissibleArtinianPureDegreesLinear Module := E -> (
    
    R := ring E;
    n := numgens R - 1;
    r := rank E;
    bettiNumbers := flatten entries ((matrix betti (resE:= res E))^{0});
    degreeGensE := first unique flatten degrees resE_0;
    
    output := {};
    root := for i from 0 to n list i;
    d := n+1;
    stop := false;
    while not stop do
    (
	currentDegrees := root | {d};
	currentPureBetti := makePureBetti (currentDegrees,TableEntries=>RealizationModules);
	currentPureBettiLeastInteger := makePureBetti (currentDegrees);
	q := lift(currentPureBetti#0,ZZ)//(currentPureBettiLeastInteger#0);
	if currentPureBetti#0 < bettiNumbers#0 and currentPureBetti#1 < bettiNumbers#1 then
	(
	   output = output | {(currentDegrees,q)};
	    d = d+1
	)
        else
	(
	    stop = true;  
	);
    );
    
    return output;
)


----------------------------------------------------------------------------------------------------
----------          CORANK 2 ANTISYMMETRIC MATRIX                                         ----------
----------------------------------------------------------------------------------------------------
corank2AntiSymmetricMatrix = method(TypicalValue => Matrix,Options=>{CoefficientRing=>ZZ/10007,Density=>1.,})

corank2AntiSymmetricMatrix ZZ := opts -> d -> (

    x := local x;
    R := opts.CoefficientRing[x_0..x_3];
    
    return corank2AntiSymmetricMatrix(d,R,Density=>opts.Density);
)

corank2AntiSymmetricMatrix (ZZ,PolynomialRing) := opts -> (d,R) -> (
    
    if numgens R != 4 then error "coordinate ring of the projective 3-space expected";
    
    KK := coefficientRing(R);
    local vectorBundle; local E; local M;
    if d == 10 then
    (
       try vectorBundle = tHooftInstantonBundle(R,2) then
       (
       	   E = (module vectorBundle)**R^{2};
       	   M = (minimalPresentation HH^2(vectorBundle(>=-4)))**R^{-3};
       )
       else
       (
	    print "\t-- failure of the random construction (try again!)";
	    return null;
       );
    )
    else if d == 14 then
    (
       try vectorBundle = ellipticInstantonBundle(R) then
       (
       	   E = (module vectorBundle)**R^{3};
       	   M = (minimalPresentation HH^2(vectorBundle(>=-4)))**R^{-4};
       )
       else
       (
	    print "\t-- failure of the random construction (try again!)";
	    return null;
       );
    )
    else
    (
       error "size ofthe matrix has to be 10 or 14";	
    );
    
    H := basis(0,Hom(E,M));
    mu := homomorphism (H*random(R^{numColumns H:0},R^{1:0},Density=>opts.Density));       
    F := minimalPresentation ker mu;
    
    try A := submatrixByDegrees(presentation F,0,1) then
    (
        try skewSymA := antiSymmetrization A then
	(
	    if numColumns skewSymA == d and numRows skewSymA == d then
	    (
	    	return skewSymA; 
	    )
	    else
	    (
	    	print "\t-- failure of the random construction (try again!)";
	    	return null;
	    );   
	)
 	else
	(
	    print "\t-- failure of the random construction (try again!)";
	    return null;
	);
    )
    else
    (
     	print "\t-- failure of the random construction (try again!)";
	return null;
    );   
)

----------------------------------------------------------------------------------------------------
----------          CORANK 1 WESTWICK MATRIX                                              ----------
----------------------------------------------------------------------------------------------------

corank1WestwickMatrix = method(TypicalValue => Matrix,Options=>{CoefficientRing=>ZZ/10007})

corank1WestwickMatrix (ZZ,ZZ) := opts -> (r,n) -> (
    
    if n < 1 then error "positive number of variables expected";
    x := local x;
    R := opts.CoefficientRing[x_0..x_n];
    
    return corank1WestwickMatrix(r,R);
)

corank1WestwickMatrix (ZZ,PolynomialRing) := opts -> (r,R) -> (
    
    n := numgens R - 1;
    if n < 1 then error "positive number of variables expected";
    if r < 1 then error "positive number expected";
    
    M := for i from 0 to r*n list
             for j from 0 to r*n+n-2 list
       	         if j-i+1 < 0 or j-i+1 > n then 0 else ( if (j+1)%(r+1)==0 then ((j+1)//(r+1)-j+i-1)*R_(j-i+1) else R_(j-i+1) );
    return matrix M;
)


----------------------------------------------------------------------------------------------------
----------          CONSTANT RANK MATRIX                                                  ----------
----------------------------------------------------------------------------------------------------

constantRankMatrix = method(TypicalValue => Matrix,Options=>{Display=>true,CheckingLevel=>0})

constantRankMatrix (Module,List,ZZ) := opts -> (E,L,q) ->
(
    R := ring(E);
    KK := coefficientRing R;
    
    resE := res minimalPresentation E;
    degreeGensE := unique flatten degrees resE_0;
    degreeSyzE := unique flatten degrees resE_1;
    if opts.CheckingLevel < 1 then
    (
        if #degreeGensE > 1 then
        (
	   if opts.Display then print "\t-- the source module has generators of more than one degree => FAIL";
	   return null;
        )
        else
        (
	    if opts.Display then print ("\t-- the source module is generated in degree " | toString(degreeGensE#0));
    	);
    
        if #degreeSyzE > 1 or (#degreeSyzE == 1 and degreeSyzE#0-degreeGensE#0 != 1) then 
	(
    	    if opts.Display then print "\t-- the source module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if opts.Display then print "\t-- the source module is linearly presented";	
    	);
    );

    G := minimalPresentation randomSocleModule(L,q,CoefficientRing=>KK);
    if opts.Display then print("\t\t-- random Artinian module generated");
    S := ring(G);
    G = (minimalPresentation coker sub(presentation G,for i from 0 to numgens(R)-1 list S_i=>R_i))**R^{-degreeGensE};
    resG := res G;
    degreeGensG := unique flatten degrees resG_0;
    degreeSyzG := unique flatten degrees resG_1;
    degreeSecondSyzG := unique flatten degrees resG_2;
    if opts.CheckingLevel < 2 then
    (
    	if #degreeGensG > 1 then 
	(
	    if opts.Display then print "\t-- the target module has generators of more than one degree => FAIL";
	    return null;
    	)
        else
    	(
	    if opts.Display then print ("\t-- the target module is generated in degree " | toString(degreeGensG#0));
        );
    
    	if #degreeSyzG > 1 or (#degreeSyzG == 1 and degreeSyzG#0-degreeGensG#0 != 1) then
	(
    	    if opts.Display then print "\t-- the target module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if #degreeSecondSyzG > 1 or (#degreeSecondSyzG == 1 and degreeSecondSyzG#0-degreeSyzG#0 != 1) then 
	    (
    	    	if opts.Display then print "\t-- the target module is not 2-linearly presented => FAIL";
	    	return null;
    	    )
            else
	    (
	    	if opts.Display then print "\t-- the target module is 2-linearly presented"; 
 	    );
        );
    );

    return constantRankMatrix(E,G,CheckingLevel=>max(opts.CheckingLevel,2),Display=>opts.Display);
);

constantRankMatrix (Module,Module) := opts -> (inputE,inputG) -> (
       
    if (R := ring inputE) =!= ring inputG then error "expected modules over the same ring";
    KK := coefficientRing R;
    
    E := minimalPresentation inputE;
    resE := res E;
    degreeGensE := unique flatten degrees resE_0;
    degreeSyzE := unique flatten degrees resE_1;
    if opts.CheckingLevel < 1 then
    (
        if #degreeGensE > 1 then
        (
	   if opts.Display then print "\t-- the source module has generators of more than one degree => FAIL";
	   return null;
        )
        else
        (
	    if opts.Display then print ("\t-- the source module is generated in degree " | toString(degreeGensE#0));
    	);
    
        if #degreeSyzE > 1 or (#degreeSyzE == 1 and degreeSyzE#0-degreeGensE#0 != 1) then 
	(
    	    if opts.Display then print "\t-- the source module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if opts.Display then print "\t-- the source module is linearly presented";	
    	);
    );

    G := minimalPresentation inputG;
    resG := res G;
    degreeGensG := unique flatten degrees resG_0;
    degreeSyzG := unique flatten degrees resG_1;
    degreeSecondSyzG := unique flatten degrees resG_2;
    if opts.CheckingLevel < 2 then
    (
    	if #degreeGensG > 1 then 
	(
	    if opts.Display then print "\t-- the target module has generators of more than one degree => FAIL";
	    return null;
    	)
        else
    	(
	    if opts.Display then print ("\t-- the target module is generated in degree " | toString(degreeGensG#0));
        );
    
    	if #degreeSyzG > 1 or (#degreeSyzG == 1 and degreeSyzG#0-degreeGensG#0 != 1) then
	(
    	    if opts.Display then print "\t-- the target module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if #degreeSecondSyzG > 1 or (#degreeSecondSyzG == 1 and degreeSecondSyzG#0-degreeSyzG#0 != 1) then 
	    (
    	    	if opts.Display then print "\t-- the target module is not 2-linearly presented => FAIL";
	    	return null;
    	    )
            else
	    (
	    	if opts.Display then print "\t-- the target module is 2-linearly presented"; 
 	    );
        );
    );

    if opts.CheckingLevel < 3 then
    (
        if degreeGensE#0 != degreeGensG#0 then 
	(
    	    if opts.Display then print "\t-- the source module and target module are generated in different degrees => FAIL";
	    return null;  
        );	
    );

    H := basis(0,Hom(E,G));
    h := homomorphism (H*random(R^{numColumns H:0},R^{1:0}));
    if opts.Display then print("\t\t-- random degree zero homomorphism generated");
    return constantRankMatrix(E,G,h,CheckingLevel=>max(opts.CheckingLevel,3),Display=>opts.Display);   
)

constantRankMatrix (Module,Module,Matrix) := opts -> (inputE,inputG,mu) -> (
    
    if (R := ring inputE) =!= ring inputG then error "expected modules over the same ring";
    
    E := minimalPresentation inputE;
    resE := res E;
    degreeGensE := unique flatten degrees resE_0;
    degreeSyzE := unique flatten degrees resE_1;
    if opts.CheckingLevel < 1 then
    (
        if #degreeGensE > 1 then
        (
	   if opts.Display then print "\t-- the source module has generators of more than one degree => FAIL";
	   return null;
        )
        else
        (
	    if opts.Display then print ("\t-- the source module is generated in degree " | toString(degreeGensE#0));
    	);
    
        if #degreeSyzE > 1 or (#degreeSyzE == 1 and degreeSyzE#0-degreeGensE#0 != 1) then 
	(
    	    if opts.Display then print "\t-- the source module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if opts.Display then print "\t-- the source module is linearly presented";	
    	);
    );

    G := minimalPresentation inputG;
    resG := res G;
    degreeGensG := unique flatten degrees resG_0;
    degreeSyzG := unique flatten degrees resG_1;
    degreeSecondSyzG := unique flatten degrees resG_2;
    if opts.CheckingLevel < 2 then
    (
    	if #degreeGensG > 1 then 
	(
	    if opts.Display then print "\t-- the target module has generators of more than one degree => FAIL";
	    return null;
    	)
        else
    	(
	    if opts.Display then print ("\t-- the target module is generated in degree " | toString(degreeGensG#0));
        );
    
    	if #degreeSyzG > 1 or (#degreeSyzG == 1 and degreeSyzG#0-degreeGensG#0 != 1) then
	(
    	    if opts.Display then print "\t-- the target module is not linearly presented => FAIL";
	    return null;
    	)
        else
        (
    	    if #degreeSecondSyzG > 1 or (#degreeSecondSyzG == 1 and degreeSecondSyzG#0-degreeSyzG#0 != 1) then 
	    (
    	    	if opts.Display then print "\t-- the target module is not 2-linearly presented => FAIL";
	    	return null;
    	    )
            else
	    (
	    	if opts.Display then print "\t-- the target module is 2-linearly presented"; 
 	    );
        );
    );

    if opts.CheckingLevel < 3 then
    (
        if degreeGensE#0 != degreeGensG#0 then 
	(
    	    if opts.Display then print "\t-- the source module and target module are generated in different degrees => FAIL";
	    return null;  
        );	
    );

    resMu := res mu;
    if opts.CheckingLevel < 4 then
    (
    	if minimalPresentation coker mu != 0 then 
	(
    	    if opts.Display then print "\t-- the morphism is not surjective => FAIL";
	    return null;  
    	)
        else
        (
    	    if opts.Display then print "\t-- the morphism is surjective";
        );
    ); 
    
    if opts.CheckingLevel < 5 then
    (
    	if minimalPresentation coker (resMu#1) != 0 then 
	(
    	    if opts.Display then print "\t-- the morphism induced on the first syzygy modules is not surjective => FAIL";
	    return null;
    	)
        else
        (
    	    if opts.Display then print "\t-- the morphism induced on the first syzygy modules is surjective";
        );
    );

    if opts.CheckingLevel < 6 then
    (
    	J2 := image resE.dd_2;
    	K2 := image resG.dd_2;
    	nu2 := map(K2,J2,resMu#2);
    
        --print(hilbertPolynomial(cokernel nu2,Projective=>false));
	if hilbertPolynomial(cokernel nu2,Projective=>false) != 0 then 
	(
    	    if opts.Display then print "\t-- the morphism induced on the images of the 2nd sygyzy maps has not artinian cokernel => FAIL";
	    return null;
    	)
        else
        (
      	    if opts.Display then print "\t-- the morphism induced on the images of the 2nd sygyzy maps has artinian cokernel";
        );
    );

    M := presentation minimalPresentation ker mu;
    return submatrixByDegrees(M,degreeGensE#0,degreeGensE#0+1);
)

--------------------------------------------------------------------------------
---- AUXILIARY FUNCTIONS                                                    ----
--------------------------------------------------------------------------------

antiSymmetrization = method(TypicalValue => Matrix)
antiSymmetrization (Matrix) := (f) -> (
   
   R := ring(f);
   U := (coefficientRing(R))[Variables=>3];
   sigma := transpose random(U^{4:1},U^{0});
   SIGMA := map(U,R,sigma);
   F := SIGMA(f);
   
   ---------- 2. Take a morphism from coker F to coker transpose F
   H := Hom(coker F,coker transpose F);      
   K := matrix homomorphism H_{0};
   
   detK := det K;
   if first degree detK != 0 or detK == 0  then error "unable to antisymmetrize";
   
   ---------- 3. Skew symmetrize
   Klift := substitute(K,R);
   A := (Klift*f);
   
   return map(R^{numRows f:0},R^{numColumns f:-1},A);
) -- END antiSymmetrization (Matrix)