newPackage("MLdegreeFermatHypersurface",
     Version => "1.0", 
     Date => "April 2014",
     Authors => {
	         {Name => "Daniele Agostini", Email => "daniele.agostini@sns.it"},
                 {Name => "Davide Alberelli", Email => "davide.alberelli@gmail.com"},
                 {Name => "Francesco Grande", Email => "fgrande@zedat.fu-berlin.de"},
                 {Name => "Paolo Lella", Email => "paolo.lella@unito.it"}
                },
     Headline => "a package for computing the maximum likelihood degree of Fermat hypersurfaces",
     DebuggingMode => false
     )
 
export {
     "MLdegFermat",
     "likelihoodCorrespondenceFermat",
     "fiberLikelihoodCorrespondenceFermat",
     "genericFiberLikelihoodCorrespondenceFermat",
     "specialFiberLikelihoodCorrespondenceFermat"
}

 
-----------------------------------------------------------------------------
----          MAXIMUM LIKELIHOOD DEGREE OF FERMAT HYPERSURFACES          ----
-----------------------------------------------------------------------------
MLdegFermat = method(TypicalValue=>ZZ,Options=>{Strategy=>0,CoefficientRing=>QQ})
 
MLdegFermat (ZZ,ZZ) := opts -> (n,d) -> (

  if n < 2 then error "at least 3 variables expected";
  
  if d < 2 then error "at least degree 2 expected";
  
  if opts.Strategy == 0 then -- best case-by-case strategy
  (
      if d == 2 then return MLdegN2(n);
      
      if n == 2 then return MLdeg2D(d);
      
      return MLdegFermat(n,d,Strategy=>6,CoefficientRing=>opts.CoefficientRing);   
  )
  else if opts.Strategy == 1 then -- multidegree
  (
      LC := likelihoodCorrespondenceFermat(n,d,CoefficientRing=>opts.CoefficientRing);
      return leadCoefficient(multidegree LC);   
  )
  else if opts.Strategy == 2 then -- multidegree, computed by difference (without saturation w.r.t. x_0 + ... + x_n)
  (
      LCpreSat := likelihoodCorrespondenceFermatPreSaturation(n,d,CoefficientRing=>opts.CoefficientRing);
      return leadCoefficient( ( multidegree (LCpreSat#0) ) - ( multidegree (LCpreSat#0 + ideal(LCpreSat#1)) ) );
  )
  else if opts.Strategy == 3 then -- degree of the generic fiber
  (
      genericFiber := genericFiberLikelihoodCorrespondenceFermat(n,d,CoefficientRing=>opts.CoefficientRing);
      return (hilbertPolynomial(genericFiber))(0);   
  )
  else if opts.Strategy == 4 then -- degree of the generic fiber, computed by difference (without saturation w.r.t. x_0 + ... + x_n)
  (
      genericFiberPreSat := genericFiberLikelihoodCorrespondenceFermatPreSaturation(n,d,CoefficientRing=>opts.CoefficientRing);
      notAdmissiblePoints := idealOfPointsLyingOnHyperplaneArrangement(n,d,CoefficientRing=>opts.CoefficientRing);
      
     return (hilbertPolynomial(genericFiberPreSat#0) - hilbertPolynomial(notAdmissiblePoints))(0);   
  )
  else if opts.Strategy == 5 then -- degree of the special fiber [1:...:1] by partitioning the solutions
  (
      MLdeg5 := 0;
      Pnd5 := limitedPartitions(n,d);
      for a in Pnd5 do
      (
         Ca := numberOfRealPermutations(a);
	 Oa := numberOfSymmetriesOfPartition(a); 
	 aCriticalPointsGerms := idealOfGermPoints(a,d);
	 MLdeg5 = MLdeg5 + Ca*((hilbertPolynomial(aCriticalPointsGerms))(0)//Oa);	  
      );
      return MLdeg5; 
  )
  else if opts.Strategy == 6 then -- degree of the special fiber [1:...:1] by partitioning the solutions, computed by difference (without saturation w.r.t. x_0 + ... + x_n)
  (
      MLdeg6 := 0;
      Pnd6 := limitedPartitions(n,d);
      for a in Pnd6 do
      (
	 Ca := numberOfRealPermutations(a);
	 Oa := numberOfSymmetriesOfPartition(a); 
  	 aCriticalPointsGermsS := idealOfGermPointsPreSaturation(a,d);
	 MLdeg6 = MLdeg6 + Ca*((hilbertPolynomial(aCriticalPointsGermsS#0) - hilbertPolynomial( aCriticalPointsGermsS#0 + ideal(aCriticalPointsGermsS#1))) 0)//Oa;	
      );
      return MLdeg6;
  )    
  else
  (
     error "unknown option";   
  );     
      
)

--------------------------------------------------------
----          CLOSED FORMULAS (unexported)          ----
--------------------------------------------------------
MLdegN2 = method(TypicalValue=>ZZ)
MLdegN2 ZZ := n -> ( return 2^n-2;)

MLdeg2D = method(TypicalValue=>ZZ)
MLdeg2D ZZ := d -> ( 

   mod6 := d % 6;
   MLdeg := d^2+d;

   if mod6 == 1 then 
   (
      return (MLdeg-5); 
   )
   else if mod6 == 4 then
   (
      return (MLdeg-2);
   )
   else if mod6 == 3 or mod6 == 5 then
   (
      return (MLdeg-3); 
   )
   else
   (
      return MLdeg;   
   );       
)

----------------------------------------------------
----          LIKELIHOOD CORRESPONDENCE         ----
----------------------------------------------------

likelihoodCorrespondenceFermat = method(TypicalValue=>Ideal,Options=>{CoefficientRing=>QQ})

likelihoodCorrespondenceFermat (ZZ,ZZ) := opts -> (n,d) -> (
        
   return saturate likelihoodCorrespondenceFermatPreSaturation (n,d,CoefficientRing=>opts.CoefficientRing);
   
)  -- END likelihoodCorrespondenceFermat (ZZ,ZZ)


likelihoodCorrespondenceFermat (PolynomialRing,PolynomialRing,ZZ) := opts -> (R,U,d) -> (
        	
   return saturate likelihoodCorrespondenceFermatPreSaturation (R,U,d,CoefficientRing=>opts.CoefficientRing);
   
)  -- END likelihoodCorrespondenceFermat (PolynomialRing,PolynomialRing,ZZ)


----------------------------------------     unexported     ----------------------------------------
likelihoodCorrespondenceFermatPreSaturation = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ})

likelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ) := opts -> (n,d) -> (
        
   if n < 2 then error "at least 3 variables expected";
  
   if d < 2 then error "at least degree 2 expected";
   
   x := local x;
   y := local y;
   
   R := (opts.CoefficientRing)[x_0..x_n,y_0..y_n,Degrees=>toList(n+1:{1,0})|toList(n+1:{0,1})];
   
   row1 := for i from n+1 to 2*n+1 list R_i;
   row2 := for i from 0 to n list R_i;
   row3 := for i from 0 to n list R_i^d;
   
   M := matrix({row1,row2,row3});
   F := sum(row3);
   H := sum(row2);
   
   I := ideal(F) + minors(3,M);
   return (I,H);
   
)  -- END likelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ)

likelihoodCorrespondenceFermatPreSaturation (PolynomialRing,PolynomialRing,ZZ) := opts -> (R,U,d) -> (
        	
   if numgens(R) < 3 then error "at least 3 variables expected";
   n := numgens(R)-1;
   
   if numgens(U) != n+1 then error "not compatible rings";
   
   if d < 2 then error "at least degree 2 expected";
   
   RU := (opts.CoefficientRing)[gens(R)|gens(U),Degrees=>toList(n+1:{1,0})|toList(n+1:{0,1})];
   
   row1 := for i from n+1 to 2*n+1 list RU_i;
   row2 := for i from 0 to n list RU_i;
   row3 := for i from 0 to n list RU_i^d;
   
   M := matrix({row1,row2,row3});
   F := sum(row3);
   H := sum(row2);
   
   I := ideal(F) + minors(3,M);
   return (I,H);
   
)  -- END likelihoodCorrespondenceFermatPreSaturation (PolynomialRing,PolynomialRing,ZZ)
----------------------------------------------------------------------------------------------------

--------------------------------------------------------------------------------------------------------
----          FIBERS OF THE PROJECTION OF THE LIKELIHOOD CORRESPONDENCE ONTO THE DATA SPACE         ----
--------------------------------------------------------------------------------------------------------

fiberLikelihoodCorrespondenceFermat = method(TypicalValue=>Ideal,Options=>{CoefficientRing=>QQ})

fiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ,List) := opts -> (R,d,u) -> (
  
   return saturate fiberLikelihoodCorrespondenceFermatPreSaturation(R,d,u,CoefficientRing=>opts.CoefficientRing);
    
) -- END fiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ,List)

fiberLikelihoodCorrespondenceFermat (ZZ,ZZ,List) := opts -> (n,d,u) -> (
  
   return saturate fiberLikelihoodCorrespondenceFermatPreSaturation(n,d,u,CoefficientRing=>opts.CoefficientRing);
   
) -- END fiberLikelihoodCorrespondenceFermat (ZZ,ZZ,List)


genericFiberLikelihoodCorrespondenceFermat = method(TypicalValue=>Ideal,Options=>{CoefficientRing=>QQ})

genericFiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ) := opts -> (R,d) -> (
  
   return  saturate genericFiberLikelihoodCorrespondenceFermatPreSaturation(R,d,CoefficientRing=>opts.CoefficientRing);
   
)  -- END genericFiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ)

genericFiberLikelihoodCorrespondenceFermat (ZZ,ZZ) := opts -> (n,d) -> (
  
   return  saturate genericFiberLikelihoodCorrespondenceFermatPreSaturation(n,d,CoefficientRing=>opts.CoefficientRing);
   
) -- END genericFiberLikelihoodCorrespondenceFermat (ZZ,ZZ)


specialFiberLikelihoodCorrespondenceFermat = method(TypicalValue=>Ideal,Options=>{CoefficientRing=>QQ})

specialFiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ) := opts -> (R,d) -> (
  
   return saturate specialFiberLikelihoodCorrespondenceFermatPreSaturation(R,d,CoefficientRing=>opts.CoefficientRing);
   
)  -- END specialFiberLikelihoodCorrespondenceFermat (PolynomialRing,ZZ)

specialFiberLikelihoodCorrespondenceFermat (ZZ,ZZ) := opts -> (n,d) -> (
       
   return saturate specialFiberLikelihoodCorrespondenceFermatPreSaturation(n,d,CoefficientRing=>opts.CoefficientRing);

)  -- END specialFiberLikelihoodCorrespondenceFermat (ZZ,ZZ)


----------------------------------------     unexported     ----------------------------------------
fiberLikelihoodCorrespondenceFermatPreSaturation = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ})

fiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ,List) := opts -> (R,d,u) -> (
  
   n := numgens(R)-1;
   
   if n < 2 then error "at least 3 variables expected";
  
   if d < 2 then error "at least degree 2 expected";
     
   if #u != numgens(R) then error "not compatible data array";
   
   KK := coefficientRing(R);
   row1 := for c in u list promote(c,KK);
   row2 := for i from 0 to n list R_i;
   row3 := for i from 0 to n list R_i^d;
   
   M := matrix({row1,row2,row3});
   F := sum(row3);
   H := sum(row2);
   
   I := ideal(F) + minors(3,M);
   return (I,H); 

)  -- END fiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ,List)

fiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ,List) := opts -> (n,d,u) -> (
  
   if n < 2 then error "at least 3 variables expected";
  
   x := local x;
   R := (opts.CoefficientRing)[x_0..x_n];
   
   return fiberLikelihoodCorrespondenceFermatPreSaturation(R,d,u,CoefficientRing=>opts.CoefficientRing);
)  -- END fiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ,List)
----------------------------------------------------------------------------------------------------


----------------------------------------     unexported     ----------------------------------------
genericFiberLikelihoodCorrespondenceFermatPreSaturation = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ})

genericFiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ) := opts -> (R,d) -> (
  
   n := numgens(R)-1;
   
   if n < 2 then error "at least 3 variables expected";
  
   if d < 2 then error "at least degree 2 expected";
   
   KK := coefficientRing(R);
   u := for i from 0 to n list random(KK);  

   return fiberLikelihoodCorrespondenceFermatPreSaturation(R,d,u,CoefficientRing=>opts.CoefficientRing);

)  -- END genericFiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ)

genericFiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ) := opts -> (n,d) -> (
  
   if n < 2 then error "at least 3 variables expected";
  
   x := local x;
   R := (opts.CoefficientRing)[x_0..x_n];
  
   u := for i from 0 to n list random(opts.CoefficientRing);
     
   return fiberLikelihoodCorrespondenceFermatPreSaturation(R,d,u,CoefficientRing=>opts.CoefficientRing);

) -- END genericFiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ)
----------------------------------------------------------------------------------------------------


----------------------------------------     unexported     ----------------------------------------
specialFiberLikelihoodCorrespondenceFermatPreSaturation = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ})

specialFiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ) := opts -> (R,d) -> (
  
   n := numgens(R)-1;
   
   if n < 2 then error "at least 3 variables expected";
  
   if d < 2 then error "at least degree 2 expected";
   
   KK := coefficientRing(R);
   u := for i from 0 to n list 1_KK;  

   return fiberLikelihoodCorrespondenceFermatPreSaturation (R,d,u,CoefficientRing=>opts.CoefficientRing);

)  -- END specialFiberLikelihoodCorrespondenceFermatPreSaturation (PolynomialRing,ZZ) 

specialFiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ) := opts -> (n,d) -> (
  
   if n < 2 then error "at least 3 variables expected";
  
   x := local x;
   R := (opts.CoefficientRing)[x_0..x_n];
  
   u := for i from 0 to n list 1_(opts.CoefficientRing);
     
   return fiberLikelihoodCorrespondenceFermatPreSaturation(R,d,u,CoefficientRing=>opts.CoefficientRing);

)  -- END specialFiberLikelihoodCorrespondenceFermatPreSaturation (ZZ,ZZ)
----------------------------------------------------------------------------------------------------


-----------------------------------------------------------------
----          IDEAL OF POINTS TO DISCARD (unexported)        ----
-----------------------------------------------------------------

idealOfPointsLyingOnHyperplaneArrangement = method(TypicalValue=>Ideal,Options=>{CoefficientRing=>QQ})

idealOfPointsLyingOnHyperplaneArrangement (PolynomialRing,ZZ) := opts -> (R,d) -> (
 
   n := numgens(R)-1;
   
   if n < 2 then error "at least 3 variables expected";
  
   if d < 2 then error "at least degree 2 expected";
     
   row2 := for i from 0 to n list R_i;
   row3 := for i from 0 to n list R_i^d;
   
   M := matrix({row2,row3});
   H := sum(row2);
   F := sum(row3);
   
   return (ideal(H,F) + minors(2,M)); 

)  -- END idealOfPointsLyingOnHyperplaneArrangement (PolynomialRing,ZZ)

idealOfPointsLyingOnHyperplaneArrangement (ZZ,ZZ) := opts -> (n,d) -> (

   if n < 2 then error "at least 3 variables expected";
  
   x := local x;
   R := (opts.CoefficientRing)[x_0..x_n];
  
   return idealOfPointsLyingOnHyperplaneArrangement(R,d);
       
)  -- END idealOfPointsLyingOnHyperplaneArrangement (ZZ,ZZ)



------------------------------------------------------
--          AUXILIARY METHODS (unexported)          --
------------------------------------------------------

limitedPartitions = method(TypicalValue=>List) -- Partitions of bounded length
limitedPartitions (ZZ,ZZ) := (n,d) -> (
  allPartition := partitions(n+1);
  return (select(allPartition, i -> #i > 1 and #i <= d));
) -- END limitedPartitions


numberOfRealPermutations = method(TypicalValue=>ZZ) -- Number of critical points with a given germ point
numberOfRealPermutations (Partition) := P -> (
    
   total := 0;
   for i from 0 to #P-1 do total = total + P#i;
   
   nop := 1_ZZ;
   for i from 1 to #P-1 do 
   (
       nop = nop*binomial(total,P#-i);
       total = total - P#-i;
   );   

   return nop;
)  -- END numberOfRealPermutations (Partition)


numberOfSymmetriesOfPartition = method(TypicalValue=>ZZ) -- Number of germ points giving the same critical points
numberOfSymmetriesOfPartition (Partition) := P -> (
    nos := 1_ZZ;
    i := 0;
    while i < #P do
    (
	j := i+1;
	while j < #P and P#j == P#i do j = j+1;
	
	nos = (j-i)!*nos;
	
	i = j;
    );
    return nos;
)  -- END numberOfSymmetriesOfPartition (Partition) 


idealOfGermPointsPreSaturation = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ}) -- Ideal of germ points (pre saturation)
idealOfGermPointsPreSaturation (Partition,ZZ) := opts -> (P,d) -> (
    
    z := local z;
    X := QQ[Variables=>(#P),VariableBaseName=>z];
    
    F := P_0*X_0^d;
    H := P_0*X_0;
    for i from 1 to #P-1 do 
    (
	F = F + P_i*X_i^d;
        H = H + P_i*X_i;
    );

    if (#P == 2) then return (ideal(F),H);

    MLdegIdeal := ideal(F);

    for dk from d-#P+1 to d-2 do
    (
	k := d-dk+1;
	Xk :=  QQ[Variables=>k];
	G := sum(first entries basis(dk,Xk));
	
	subsetsKvariables := subsets(gens(X),k);
	for i from 0 to #subsetsKvariables-1 do 
	(
	    mapXktoX := map(X,Xk,subsetsKvariables#i);
	    MLdegIdeal =  trim (MLdegIdeal + ideal(mapXktoX(G)));
	);
    );
    
    allDifferentVariables := subsets(gens(X),2);
    for i from 0 to #allDifferentVariables-1 do MLdegIdeal =  saturate(MLdegIdeal,allDifferentVariables#i#0-allDifferentVariables#i#1);
    
    return (MLdegIdeal,H);
    
) -- END idealOfGermPointsPreSaturation (Partition,ZZ)


idealOfGermPoints = method(TypicalValue=>Sequence,Options=>{CoefficientRing=>QQ}) -- Ideal of germ points
idealOfGermPoints (Partition,ZZ) := opts -> (P,d) -> (
    
    return saturate idealOfGermPointsPreSaturation (P,d,CoefficientRing=>opts.CoefficientRing);
    
) -- END idealOfGermPoints (Partition,ZZ)



------------------------------------------
-----          ASSERT TESTS          -----
------------------------------------------

-- MLdegree
TEST ///
   assert(MLdegFermat(3,4) == 76);
///,

-- likelihoodCorrespondence
TEST ///
   LC := likelihoodCorrespondenceFermat(3,4);
   assert(leadCoefficient(multidegree LC) == MLdegFermat(3,4));
///,

-- fiberLikelihoodCorrespondence
TEST ///
   data := for i from 0 to 3 list random(QQ);
   fiber := fiberLikelihoodCorrespondenceFermat(3,4,data);
   assert(degree fiber == MLdegFermat(3,4));
///,

-- genericFiberLikelihoodCorrespondence
TEST ///
   genericFiber := genericFiberLikelihoodCorrespondenceFermat(3,4);
   assert(degree fiber == MLdegFermat(3,4));
///,

-- specialFiberLikelihoodCorrespondence
TEST ///
   specialFiber := specialFiberLikelihoodCorrespondenceFermat(3,4);
   assert(specialFiber == fiberLikelihoodCorrespondenceFermat(3,4,{1,1,1,1}));
   assert(degree specialFiber == MLdegFermat(3,4));
///,

-------------------------------------------
-----          DOCUMENTATION          -----
-------------------------------------------
beginDocumentation()

document { 
   Key => MLdegreeFermatHypersurface,
   Headline => "the maximum likelihood degree of Fermat hypersurfaces",
   PARA{EM "MLdegreeFermatHypersurface", " is a package designed to investigate the maximum likelihood (ML) degree
   of Fermat hypersurfaces. This code implements the algorithms presented in the paper ", 
   EM "The maximum likelihood degree of Fermat hypersurfaces",", arXiv e-prints (2014), available at ",
   TT "http://arxiv.org/abs/1404.5745","."},
   PARA{},
   SUBSECTION "List of features",
   UL{
     {"Compute the ML degree of the Fermat hypersurface ",TT "F",SUB{TT "n,d"}," of degree ",TT "d"," defined by the 
       equation ",TT "x",SUB{TT "0"},SUP{TT "d"},TT " + ... + ",TT "x",SUB{TT "n"},SUP{TT "d"},TT " = 0",BR{}," in the projective 
       space ",TT "P",SUP{TT "n"},TT " = Proj K[x",SUB{TT "0"},TT ",...,x",SUB{TT "n"},TT "]"," (see ",TO MLdegFermat,")."},
     {"Compute the ideal defining the likelihood correspondence ",TT "L",SUB{TT "n,d"}," of the Fermat hypersurface ",
       TT "F",SUB{TT "n,d"},BR{}," in the product of projective spaces ",TT "P",SUP{TT "n"},TT" x P",SUP{TT "n"},
       TT " = Proj K[x",SUB{TT "0"},TT ",...,x",SUB{TT "n"},TT "] x Proj K[u",SUB{TT "0"},TT ",...,u",SUB{TT "n"},TT "]"," (see ",TO likelihoodCorrespondenceFermat,")."},
     {"Study the fibers of the projection map ",TT "L",SUB{TT "n,d"},TT " -> P",SUP{TT "n"},TT " = Proj K[u",SUB{TT "0"},TT ",...,u",SUB{TT "n"},TT "]",BR{},
     " (see ",TO fiberLikelihoodCorrespondenceFermat,", ",TO genericFiberLikelihoodCorrespondenceFermat,", ",TO specialFiberLikelihoodCorrespondenceFermat,")."} 
   }
}

document {
   Key => {(MLdegFermat,ZZ,ZZ),MLdegFermat},
   Usage => "MLdegFermat(n,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {ZZ=>{"the maximum likelihood degree of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   MLdegFermat(n,d)
   ///
}

document {
   Key => {[MLdegFermat,Strategy]},
   Usage => "MLdegFermat(n,d,Strategy=>s)",
   Inputs => {"s" => ZZ => {"between 0 and 6."}},
   SUBSECTION "Strategy => 0 -- Default value",
   PARA{"This is the case-by-case best strategy."," For ",TT "n = 2"," and ",TT "d = 2"," there are closed formulas."," For the other cases, ",TT "Strategy=>6"," is used."},
   SUBSECTION "Strategy => 1 -- Simple 'multidegree'",
   PARA{"The ML degree of ",TT "F",SUB{TT "n,d"}," is computed as the leading coefficient of the bidegree polynomial of the likelihood correspondence ",TT "L",SUB{TT "n,d"},"."},
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3,y_0..y_n,Degrees=>{{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1},{0,1}}];
   M = matrix ({{y_0,y_1,y_2,y_3},{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   LC = saturate(I,x_0+x_1+x_2+x_3);
   bidegLC = multidegree LC 
   MLdeg = leadCoefficient bidegLC
   ///,
   SUBSECTION "Strategy => 2 -- 'Multidegree' by difference",
   PARA{"In order to avoid the saturation, the bidegree polynomial of the likelihood correspondence ",TT "L",SUB{TT "n,d"}," is computed as difference between",
   " the bidegree polynomial of the ideal before the saturation and the ideal and the ideal with the linear form added."},   
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3,y_0..y_n,Degrees=>{{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1},{0,1}}];
   M = matrix ({{y_0,y_1,y_2,y_3},{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   IH = ideal(x_0+x_1+x_2+x_3) + I;
   bidegLC = multidegree I - multidegree IH
   MLdeg = leadCoefficient bidegLC
   ///,
   SUBSECTION "Strategy => 3 -- Simple 'random data'",
   PARA{"The ML degree of ",TT "F",SUB{TT "n,d"}," is computed as the degree of the fiber of the projection ",TT "L",SUB{TT "n,d"},TT " -> P",SUP{TT "n"},
   " of a randomly chosen point."},
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3];
   u = {random(QQ),random(QQ),random(QQ),random(QQ)};
   M = matrix ({u,{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   fiber = saturate(I,x_0+x_1+x_2+x_3);
   MLdeg = (hilbertPolynomial fiber)(0)
   ///,
   SUBSECTION "Strategy => 4 -- 'Random data' by difference",
   PARA{"The degree of the fiber of the projection ",TT "L",SUB{TT "n,d"},TT " -> P",SUP{TT "n"}," of a randomly chosen point is computed ",
   "as the difference between the degree of the ideal of the fiber before the saturation and the ideal with the linear form added."},
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3];
   u = {random(QQ),random(QQ),random(QQ),random(QQ)};
   M = matrix ({u,{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   IH = ideal(x_0+x_1+x_2+x_3) + I;
   MLdeg = (hilbertPolynomial I - hilbertPolynomial IH)(0)  
   ///,
   SUBSECTION "Strategy => 5 -- Simple 'partitioning'",
   PARA{"The ML degree of ",TT "F",SUB{TT "n,d"}," is computed as the degree of the fiber of the projection ",TT "L",SUB{TT "n,d"},TT " -> P",SUP{TT "n"},
   " of the point ",TT "[1:...:1]",". The solutions of this ideal are partitioned according to the number of distinct coordinates."},
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3];
   M = matrix ({{1,1,1,1},{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   a1 = {2,1,1};
   R1 = QQ[z_1,z_2,z_3];
   phi1 = map(R1,S,{z_1,z_1,z_2,z_3});
   I1 = saturate(phi1(I),(2*z_1+z_2+z_3)*(z_1-z_2)*(z_1-z_3)*(z_2-z_3));
   ML1 = (hilbertPolynomial I1)(0)*binomial(4,2)*binomial(2,1)//(1!*2!)
   a2 = {3,1};
   R2 = QQ[z_1,z_2];
   phi2 = map(R2,S,{z_1,z_1,z_1,z_2});
   I2 = saturate(phi2(I),(3*z_1+z_2)*(z_1-z_2));
   ML2 = (hilbertPolynomial I2)(0)*binomial(4,3)//(1!*1!)
   a3 = {2,2};
   R3 = QQ[z_1,z_2];
   phi3 = map(R3,S,{z_1,z_1,z_2,z_2});
   I3 = saturate(phi3(I),(2*z_1+2*z_2)*(z_1-z_2));
   ML3 = (hilbertPolynomial I3)(0)*binomial(4,2)//(2!)
   MLdeg = ML1 + ML2 + ML3
   ///,
   SUBSECTION "Strategy => 6 -- 'Partitioning' by difference",
   PARA{"The ML degree of ",TT "F",SUB{TT "n,d"}," is computed as the degree of the fiber of the projection ",TT "L",SUB{TT "n,d"},TT " -> P",SUP{TT "n"},
   " of the point ",TT "[1:...:1]",". The solutions of this ideal are partitioned according to the number of distinct coordinates and the number of solutions with ",
   "a fixed pattern is computed as difference between the ideal before the saturation and the ideal with the linear form added."},
   EXAMPLE lines ///
   n = 3; d = 3;
   S = QQ[x_0..x_3];
   M = matrix ({{1,1,1,1},{x_0,x_1,x_2,x_3},{x_0^d,x_1^d,x_2^d,x_3^d}})
   I = ideal(x_0^d+x_1^d+x_2^d+x_3^d) + minors(3,M);
   a1 = {2,1,1};
   R1 = QQ[z_1,z_2,z_3];
   phi1 = map(R1,S,{z_1,z_1,z_2,z_3});
   I1 = saturate(phi1(I),(z_1-z_2)*(z_1-z_3)*(z_2-z_3));
   IH1 = ideal(2*z_1+z_2+z_3) + I1;
   ML1 = (hilbertPolynomial I1 - hilbertPolynomial IH1)(0)*binomial(4,2)*binomial(2,1)//(1!*2!)
   a2 = {3,1};
   R2 = QQ[z_1,z_2];
   phi2 = map(R2,S,{z_1,z_1,z_1,z_2});
   I2 = saturate(phi2(I),z_1-z_2);
   IH2 = ideal(3*z_1+z_2) + I2;
   ML2 = (hilbertPolynomial I2 - hilbertPolynomial IH2)(0)*binomial(4,3)//(1!*1!)
   a3 = {2,2};
   R3 = QQ[z_1,z_2];
   phi3 = map(R3,S,{z_1,z_1,z_2,z_2});
   I3 = saturate(phi3(I),z_1-z_2);
   IH3 = ideal(2*z_1+2*z_2) + I3;
   ML3 = (hilbertPolynomial I3 - hilbertPolynomial IH3)(0)*binomial(4,2)//(2!)
   MLdeg = ML1 + ML2 + ML3
   ///
}


document {
   Key => {[MLdegFermat,CoefficientRing]},
   Usage => "MLdegFermat(n,d,CoefficientRing=>KK)",
   Inputs => {"KK" => Ring => {"the ring of coefficients of the polynomials (usually a field)."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   MLdegFermat(n,d,CoefficientRing=>ZZ/10007)
   ///
}


document {
   Key => likelihoodCorrespondenceFermat,
   Usage => "likelihoodCorrespondenceFermat(n,d)\nlikelihoodCorrespondenceFermat(S,U,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "U"=> PolynomialRing => {"with ",TT "numgens U == numgens S",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal=>{"describing the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "P",SUP{TT "n"},TT " x P",SUP{TT "n"}," (or in the projective space ",TT "Proj S x Proj U",")."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   likelihoodCorrespondenceFermat(n,d)
   ///,
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   U = QQ[v_0..v_3];
   likelihoodCorrespondenceFermat(S,U,d)
   ///
}

document {
   Key => (likelihoodCorrespondenceFermat,ZZ,ZZ),
   Usage => "likelihoodCorrespondenceFermat(n,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal=>{"describing the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "P",SUP{TT "n"},TT " x P",SUP{TT "n"},"."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   likelihoodCorrespondenceFermat(n,d)
   ///
}

document {
   Key => (likelihoodCorrespondenceFermat,PolynomialRing,PolynomialRing,ZZ),
   Usage => "likelihoodCorrespondenceFermat(S,U,d)",
   Inputs => {"S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "U"=> PolynomialRing => {"with ",TT "numgens U == numgens S",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal=>{"describing of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "Proj S x Proj U","."}},
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   U = QQ[v_0..v_3];
   d = 2;
   likelihoodCorrespondenceFermat(S,U,d)
   ///
}

document {
   Key => [likelihoodCorrespondenceFermat,CoefficientRing],
   Headline => "",
   Usage => "likelihoodCorrespondenceFermat(n,d,CoefficientRing=>KK)",
   Inputs => {"KK" => Ring => {"the ring of coefficients of the polynomials (usually a field)."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   likelihoodCorrespondenceFermat(n,d,CoefficientRing=>ZZ/10007)
   ///
}

document {
   Key => fiberLikelihoodCorrespondenceFermat,
   Usage => "fiberLikelihoodCorrespondenceFermat(n,d,u)\nfiberLikelihoodCorrespondenceFermat(S,d,u)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1;"}, "u" => List => {"a list of ",TT "n"," numbers"}},
   Outputs => {Ideal=>{"describing the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space (or in the projective space ",TT "Proj S",") on the data space corresponding to the point whose coordinates are described by ",TT "u","."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   u = {3,5,-1,7};
   fiberLikelihoodCorrespondenceFermat(n,d,u)
   ///,
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   fiberLikelihoodCorrespondenceFermat(S,d,u)
   ///
}

document {
   Key => (fiberLikelihoodCorrespondenceFermat,ZZ,ZZ,List),
   Usage => "fiberLikelihoodCorrespondenceFermat(n,d,u)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "d" => ZZ => {"greater than 1;"}, "u" => List => {"with ",TT "n"," numbers describing the coordinates of a projective point."}},
   Outputs => {Ideal=>{"describing the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space on the data space corresponding to the point whose coordinates are described by ",TT "u","."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   u = {3,5,-1,7};
   fiberLikelihoodCorrespondenceFermat(n,d,u)
   ///
}

document {
   Key => (fiberLikelihoodCorrespondenceFermat,PolynomialRing,ZZ,List),
   Usage => "fiberLikelihoodCorrespondenceFermat(S,d,u)",
   Inputs => {"S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1."}, "u" => List => {"with ",TT "n"," numbers describing the coordinates of a projective point."}},
   Outputs => {Ideal=>{"describing the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "Proj S"," on the data space corresponding to the point whose coordinates are described by ",TT "u","."}},
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   d = 3;
   u = {3,5,-1,7};
   fiberLikelihoodCorrespondenceFermat(S,d,u)
   ///
}

document {
   Key => [fiberLikelihoodCorrespondenceFermat,CoefficientRing],
   Headline => "",
   Usage => "fiberLikelihoodCorrespondenceFermat(n,d,u,CoefficientRing=>KK)",
   Inputs => {"KK" => Ring => {"the ring of coefficients of the polynomials (usually a field)."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   u = {3,5,-1,7};
   fiberLikelihoodCorrespondenceFermat(n,d,u,CoefficientRing=>ZZ/10007)
   ///
}

document {
   Key => genericFiberLikelihoodCorrespondenceFermat,
   Usage => "genericFiberLikelihoodCorrespondenceFermat(n,d)\ngenericFiberLikelihoodCorrespondenceFermat(S,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal => {"describing the generic fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space (or in the projective space ",TT "Proj S",") on the data space."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   genericFiberLikelihoodCorrespondenceFermat(n,d)
   ///,
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   genericFiberLikelihoodCorrespondenceFermat(S,d)
   /// 
}

document {
   Key => (genericFiberLikelihoodCorrespondenceFermat,ZZ,ZZ),
   Usage => "genericFiberLikelihoodCorrespondenceFermat(n,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal => {"describing of the generic fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space on the data space."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   genericFiberLikelihoodCorrespondenceFermat(n,d)
   ///
}

document {
   Key => (genericFiberLikelihoodCorrespondenceFermat,PolynomialRing,ZZ),
   Usage => "genericFiberLikelihoodCorrespondenceFermat(S,d)",
   Inputs => {"S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal => {"describing of the generic fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "Proj S"," on the data space."}},
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   d = 2;
   genericFiberLikelihoodCorrespondenceFermat(S,d)
   ///
}

document {
   Key => [genericFiberLikelihoodCorrespondenceFermat,CoefficientRing],
   Headline => "",
   Usage => "genericFiberLikelihoodCorrespondenceFermat(n,d,CoefficientRing=>KK)",
   Inputs => {"KK" => Ring => {"the ring of coefficients of the polynomials (usually a field)."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   genericFiberLikelihoodCorrespondenceFermat(n,d,CoefficientRing=>ZZ/10007)
   ///
}

document {
   Key => specialFiberLikelihoodCorrespondenceFermat,
   Usage => "specialFiberLikelihoodCorrespondenceFermat(n,d)\nspecialFiberLikelihoodCorrespondenceFermat(S,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal => {"describing the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space (or in the projective space ",TT "Proj S",") on the data space corresponding to the point ",TT "[1:...:1]","."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   specialFiberLikelihoodCorrespondenceFermat(n,d)
   ///,
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   specialFiberLikelihoodCorrespondenceFermat(S,d)
   ///}

document {
   Key => (specialFiberLikelihoodCorrespondenceFermat,ZZ,ZZ),
   Usage => "specialFiberLikelihoodCorrespondenceFermat(n,d)",
   Inputs => {"n"=> ZZ => {"greater than 1;"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {Ideal => {"describing the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the ",TT "n","-dimensional projective space on the data space corresponding to the point ",TT "[1:...:1]","."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   specialFiberLikelihoodCorrespondenceFermat(n,d)
   ///
}

document {
   Key => (specialFiberLikelihoodCorrespondenceFermat,PolynomialRing,ZZ),
   Usage => "specialFiberLikelihoodCorrespondenceFermat(S,d)",
   Inputs => {"S"=> PolynomialRing => {"with ",TT "numgens S > 2",";"}, "d" => ZZ => {"greater than 1."}},
   Outputs => {{"the ideal of the fiber of the projection of the likelihood correspondence of the Fermat hypersurface of degree ",TT "d"," in the projective space ",TT "Proj S"," on the data space corresponding to the point ",TT "[1:...:1]","."}},
   EXAMPLE lines ///
   S = QQ[t_0..t_3];
   d = 2;
   specialFiberLikelihoodCorrespondenceFermat(S,d)
   ///
}

document {
   Key => {[specialFiberLikelihoodCorrespondenceFermat,CoefficientRing]},
   Headline => "",
   Usage => "specialFiberLikelihoodCorrespondenceFermat(n,d,CoefficientRing=>KK)",
   Inputs => {"KK" => Ring => {"the ring of coefficients of the polynomials (usually a field)."}},
   EXAMPLE lines ///
   n = 3;
   d = 2;
   specialFiberLikelihoodCorrespondenceFermat(n,d,CoefficientRing=>ZZ/10007)
   ///
}

end