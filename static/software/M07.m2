-- -*- coding: utf-8 -*-
newPackage("M07",
     Version => "1.0", 
     Date => "July 28, 2016",
     Authors => {{Name => "Paolo Lella", Email => "paolo.lella@unitn.it"}},
     Headline => "Ancillary file to the paper \"Towards Fulton's conjecture\""
     )
     
export {
   -- methods
   "dimAmbientSpace",
   "dimPic",
   "dimSubspaceRelations",
   "setOfIndices",
   "FnefCone",
   "linearEquivalenceRelations",
   "FontanariBasis",
   "FontanariBasisIndices",
   "FontanariBasisPositions",   
   "quotientSpace",
   "minkowskiSum",
   "indexOfContainment",
   "indexOfContainmentLinearForms",
   "Vrepresentation2Hrepresentation",
   "evaluate",
   -- options
   "LP",
   "Simplify",
   "polymake",
   "lpSolve"
   }

----------------------------------------------------------------------------------------------------
----------   DIMENSION OF THE AMBIENT SPACE                                               ----------
----------------------------------------------------------------------------------------------------
dimAmbientSpace = method(TypicalValue=>ZZ)

dimAmbientSpace ZZ := n -> (
   return 2^(n-1)-n-1;    
)

----------------------------------------------------------------------------------------------------
----------   DIMENSION OF PIC                                                             ----------
----------------------------------------------------------------------------------------------------
dimPic = method(TypicalValue=>ZZ)

dimPic ZZ := n -> (
   return 2^(n-1)-binomial(n,2)-1;    
) 

----------------------------------------------------------------------------------------------------
----------   DIMENSION OF THE SUBSPACE OF LINEAR EQUIVALENCE RELATIONS                    ----------
----------------------------------------------------------------------------------------------------
dimSubspaceRelations = method(TypicalValue=>ZZ)

dimSubspaceRelations ZZ := n -> (
   return dimAmbientSpace n - dimPic n;
) 

----------------------------------------------------------------------------------------------------
----------   INDICES LABELING VARIEBLES                                                   ----------
----------------------------------------------------------------------------------------------------
setOfIndices = method(TypicalValue=>List)

setOfIndices ZZ := n -> (
    P := for i from 1 to n list i;
    output := {};
    for k from 2 to n//2 do 
    (
    	if 2*k == n then
	(
      	    Pk := sort subsets(P,k);
      	    while #Pk > 0 do
      	    (
        	F := first Pk;
		compF := complementarySubset (F,n);
		output = output | {F};
		Pk = delete(F,Pk);
		Pk = delete(compF,Pk);	 
      	    );
    	)
        else
    	(
      	    output = output | (sort subsets(P,k));  
    	);
    );
    return sort output;
) 

----------------------------------------------------------------------------------------------------
----------   H-REPRESENTATION OF THE F-NEF CONE                                           ----------
----------------------------------------------------------------------------------------------------
FnefCone = method(TypicalValue=>List)

FnefCone (ZZ,PolynomialRing) := (n,R) -> (
    I := setOfIndices n;
    halfSpaces := {};
    for P in fourPartitions n do
    (
     	ij := position(I,x-> x == sort(P#0|P#1) or x == sort complementarySubset(P#0|P#1,n));
     	ik := position(I,x-> x == sort(P#0|P#2) or x == sort complementarySubset(P#0|P#2,n));
     	il := position(I,x-> x == sort(P#0|P#3) or x == sort complementarySubset(P#0|P#3,n));
     	H := R_ij + R_ik + R_il;
     	if #(P#0) > 1 then H = H - R_(position(I,x-> x == P#0 or x == sort complementarySubset(P#0,n)));
     	if #(P#1) > 1 then H = H - R_(position(I,x-> x == P#1 or x == sort complementarySubset(P#1,n)));
     	if #(P#2) > 1 then H = H - R_(position(I,x-> x == P#2 or x == sort complementarySubset(P#2,n)));
     	if #(P#3) > 1 then H = H - R_(position(I,x-> x == P#3 or x == sort complementarySubset(P#3,n)));
     	halfSpaces = append(halfSpaces,H);
    );
    return rsort halfSpaces;
) 

FnefCone ZZ := n -> (
    I := setOfIndices n;
    w := local w;
    R := QQ[for i in I list w_i];  
    
    return FnefCone(n,R);
) 

----------------------------------------------------------------------------------------------------
----------   LINEAR EQUIVALENCE RELATIONS                                                 ----------
----------------------------------------------------------------------------------------------------
linearEquivalenceRelations = method(TypicalValue=>List)

linearEquivalenceRelations (ZZ,PolynomialRing) := (n,R) -> (
    I := setOfIndices n;
    output := {};
    for S in sort subsets(for i from 1 to n list i,4) do
    (
     	pos := 0_R;
     	neg1 := 0_R;
     	neg2 := 0_R;
     
        for i from 0 to #I-1 do
     	(
	    T := I#i;
	    compT := complementarySubset(T,n);
	    if (isSubset({S#0,S#1},T) and isSubset({S#2,S#3},compT)) or (isSubset({S#0,S#1},compT) and isSubset({S#2,S#3},T)) then
	    (
	    	pos = pos + R_i;
	    )
            else if (isSubset({S#0,S#2},T) and isSubset({S#1,S#3},compT)) or (isSubset({S#0,S#2},compT) and isSubset({S#1,S#3},T)) then 
	    (
	    	neg1 = neg1 + R_i;
	    )
            else if (isSubset({S#0,S#3},T) and isSubset({S#1,S#2},compT)) or (isSubset({S#0,S#3},compT) and isSubset({S#1,S#2},T)) then 
	    (
	    	neg2 = neg2 + R_i;
	    );
     	);
 
        output = append(output,pos-neg1);
        output = append(output,pos-neg2);
  );
  return output;
) 

linearEquivalenceRelations ZZ := n -> (
    I := setOfIndices n;
    D := local D;
    R := QQ[for i in I list D_i];  
    
    return linearEquivalenceRelations(n,R);
) 

----------------------------------------------------------------------------------------------------
----------   FONTANARI BASIS                                                                   ----------
----------------------------------------------------------------------------------------------------
FontanariBasis = method(TypicalValue=>List)

FontanariBasis (ZZ,PolynomialRing) := (n,R) -> (
    return for p in FontanariBasisPositions n list R_p;
) 

FontanariBasis ZZ := n -> (
    I := setOfIndices n;
    D := local D;
    R := QQ[for i in I list D_i];  
    
    return FontanariBasis(n,R);
) 

FontanariBasisIndices = method(TypicalValue=>List)

FontanariBasisIndices ZZ := n -> (
    if n < 4 then return {};
    
    B' := {};
    B :=  {{2,3}};
    for m from 5 to n do 
    (
       	P3 := for i from 1 to m-3 list i;
       	P2 := for i from 1 to m-2 list i;
       
        -- First part
       	current := for g in B list g;
       
        -- Second part
       	for k from 0 to m-4 do 
       	(
	    A := subsets(P3,k);
	    current = current | for a in A list (a|{m-2,m-1});
       	);
   
        -- Third part
       	for g in B do
       	(
	    if not member(g,B') then current = current | {complementarySubset(g,m-1)};	 
       	);
       
        B' = B;
        B = current;
    );

    I := setOfIndices n;
    return sort for g in B list if member(g,I) then g else complementarySubset(g,n);
) 

FontanariBasisPositions = method(TypicalValue=>List)

FontanariBasisPositions ZZ := n -> (
   I := setOfIndices n;
   FB := FontanariBasisIndices n;
   return for s in FB list position(I,x -> x == s);
) 

----------------------------------------------------------------------------------------------------
----------   QUOTIENT SPACE REPRESENTATION                                                ----------
----------------------------------------------------------------------------------------------------

quotientSpace = method(TypicalValue=>Sequence)

quotientSpace (ZZ,List) := (n,L) -> (
    
    I := setOfIndices n;
    outsideElements := {};
    for i from 0 to dimAmbientSpace n - 1 do if not member(i,L) then outsideElements = outsideElements | {i};
    W := for i from 0 to dimAmbientSpace n - 1 list if member(i,L) then 0 else 1;
    D := local D;
    w := local w;
    C := QQ[for i in I list w_i];
    R := C[for i in I list D_i,MonomialOrder=>{Weights=>W}];
    
    -- Checking if the subspace defined by L is complementary to V_n
    V := rsort flatten entries gens trim ideal (linearEquivalenceRelations (n,R));
    M := matrix for v in V list for i in outsideElements list lift(leadCoefficient(v//R_i),QQ);
    if det M == 0 then error ("the given subspace is not complementary to V_" | toString(n));
       
    Csub := QQ[for i in L list C_i];
    Rsub := Csub[for i in L list R_i];
    
    fromCtoCsub := map(Csub,C);
    fromCsubToC := map(C,Csub);
    
    fromRtoRsub := map(Rsub,R);
    fromRsubToR := map(R,Rsub);
    imagesProjectionR := {};
    imagesProjectionC := {};
    for i from 0 to dimAmbientSpace n - 1 do
    (
    	if member(i,L) then
	(
	    imagesProjectionR = imagesProjectionR | {fromRtoRsub(R_i)};
	    imagesProjectionC = imagesProjectionC | {fromCtoCsub(C_i)};
	)
        else
	(
	    v := first V;
	    V = delete(v,V);
	    imagesProjectionR = imagesProjectionR | {fromRtoRsub(leadMonomial v - v)};
	    imagesProjectionC = imagesProjectionC | {0};
	);	
    );
    
    return ((R,Rsub,map(Rsub,R,imagesProjectionR|imagesProjectionC),fromRsubToR),(C,Csub,fromCtoCsub,fromCsubToC));
) -- END quotientSpace ZZ 


----------------------------------------------------------------------------------------------------
----------   MINKOWSKI SUM                                                                ----------
----------------------------------------------------------------------------------------------------

minkowskiSum = method (TypicalValue => List)

minkowskiSum (List,RingElement) := (C,v) -> (
    return minkowskiSum (C,{v});
)

minkowskiSum (List,List) := (C,V) -> (
    R := ring C#0;
    makeDirectory(currentDirectory() | "temp");
    VsubspaceFile := openOut(currentDirectory() | "temp/HrepresentationV.txt");
    CconeFile := openOut(currentDirectory() | "temp/HrepresentationC.txt");
    equations := subspaceEquations(V);
    S := ring equations#0;
    for e in equations do
    (
       	VsubspaceFile << "0";
       	for g in gens S do VsubspaceFile << " " | toString(leadCoefficient(e//g));
        VsubspaceFile << "\n"; 
    );
    close(VsubspaceFile);
    for c in C do
    (
    	CconeFile << "0";
	for g in gens R do CconeFile << " " | toString(leadCoefficient(c//g));
	CconeFile << "\n";	
    );
    close(CconeFile);

    commands := openOut(currentDirectory() | "minkowskiSum.txt");
    commands << "use application 'polytope';\n";
    commands << "use vars '$S', '$C', '$V';\n"; 
    commands << "open(INPUT,\"< temp/HrepresentationV.txt\");\n";
    commands << "$V = new Polytope<Rational>(INEQUALITIES=>[[1";
    for g in gens R do commands << ",0";
    commands << "]],EQUATIONS=>new Matrix<Rational>(<INPUT>));\n";
    commands << "close(INPUT);\n";
    commands << "open(INPUT,\"< temp/HrepresentationC.txt\");\n";
    commands << "$C = new Polytope<Rational>(INEQUALITIES=>new Matrix<Rational>(<INPUT>));\n";
    commands << "close(INPUT);\n";
    commands << "$S = minkowski_sum($C,$V);\n";
    commands << "open(OUTPUT,\"> temp/HrepresentationCplusV.txt\");\n";
    commands << "print OUTPUT $S->FACETS;\n";
    commands << "close(OUTPUT);\n";
    commands << "exit();\n";
    close(commands);
    
    run "polymake --script minkowskiSum.txt > logMinkowskiSum.txt";
    run "rm minkowskiSum.txt logMinkowskiSum.txt";
    
    L := lines get (currentDirectory() | "temp/HrepresentationCplusV.txt");
    CplusV := {};
    for l in L do
    (
       	t := value replace(" ",",","{"|l|"}");
	t = (1/gcd t)*t;
       	if t#0 == 0 then CplusV = CplusV | {sum(for i from 1 to #t-1 list t#i*R_(i-1))};
    );

    run "rm -r temp";
    return rsort CplusV;
) 

----------------------------------------------------------------------------------------------------
----------   INDEX OF CONTAINMENT                                                         ----------
----------------------------------------------------------------------------------------------------

indexOfContainment = method(TypicalValue => ZZ, Options=>{LP=>polymake})

indexOfContainment (List,List) := opts -> (F,C) -> (
    
    R := ring(C#0);
    
    makeDirectory(currentDirectory() | "temp");
    FconeFile := openOut(currentDirectory() | "temp/HrepresentationF.txt");
    CconeFile := openOut(currentDirectory() | "temp/HrepresentationC.txt");
    if opts.LP == polymake then
    (
	for f in F do
    	(
	    FconeFile << "0";
	    for g in gens R do FconeFile << " " | toString(leadCoefficient(f//g));
	    FconeFile << "\n";	
	);
        close(FconeFile);
        for c in C do
    	(
	    CconeFile << "0";
	    for g in gens R do CconeFile << " " | toString(leadCoefficient(c//g));
	    CconeFile << "\n";	
	);
        close(CconeFile);
	
        minimaPolymake := openOut(currentDirectory() | "/launcher.txt");
	minimaPolymake << "use application 'polytope';\n";
        minimaPolymake << "use vars '$Fnef', '$V', '$L';\n";
        minimaPolymake << "open(INPUT,\"< " | "temp/HrepresentationF.txt\");\n";
        minimaPolymake << "$Fnef = new Polytope<Rational>(INEQUALITIES=>new Matrix<Rational>(<INPUT>));\n";
	minimaPolymake << "close(INPUT);\n";
       	minimaPolymake << "open(INPUT,\"< " | "temp/HrepresentationC.txt\");\n";
        minimaPolymake << "open(OUTPUT,\"> " | "minima.txt\");\n";
	minimaPolymake << "while(<INPUT>) {\n";
	minimaPolymake << "  $V = new Vector<Rational>($_);\n";
	minimaPolymake << "  $L = $Fnef->LP(LINEAR_OBJECTIVE=>$V);\n";
	minimaPolymake << "  print OUTPUT $L->MINIMAL_VALUE;\n";
	minimaPolymake << "  print OUTPUT \"\\n\";\n";
	minimaPolymake << "}\n";
	minimaPolymake << "close(INPUT);\n";
	minimaPolymake << "close(OUTPUT);\n";
        minimaPolymake << "exit;";
	close(minimaPolymake);
		
	run "polymake --script launcher.txt > log.txt";
	run "rm launcher.txt log.txt";
    )
    else if opts.LP == lpSolve then
    (
	for f in F do
    	(
	    beginRow := true;
	    for g in gens R do
	    (
	       if beginRow then beginRow = false else FconeFile << " ";
	       FconeFile << toString(leadCoefficient(f//g)) | " " | toString(-leadCoefficient(f//g));
	    );
	    FconeFile << "\n";	
	);
        close(FconeFile);
        for c in C do
    	(
	    beginRow := true;
	    for g in gens R do
	    (
	       if beginRow then beginRow = false else CconeFile << " ";
	       CconeFile << toString(leadCoefficient(c//g)) | " " | toString(-leadCoefficient(c//g));
	    );
	    CconeFile << "\n";	
	);
        close(CconeFile);
	
	minimaR := openOut(currentDirectory() | "/launcher.R");
	minimaR << "rm(list=ls())\nlibrary(lpSolve);\n";
	minimaR << "numColumns <- " | toString(2*(numgens R)) | ";\n";
	minimaR << "a <- scan('temp/HrepresentationF.txt', sep=' ',quiet=TRUE);\n";	 
	minimaR << "problem.leftHandSide <- matrix(data=a,ncol=numColumns,byrow=TRUE);\n";
	minimaR << "numRows <- nrow(problem.leftHandSide);\n";
	minimaR << "problem.sign <- character(numRows);\n";
	minimaR << "for (i in 1:numRows) {problem.sign[i] = \">=\";}\n";
	minimaR << "problem.rightHandSide <- numeric(numRows);\n";	 
	minimaR << "b <- scan('temp/HrepresentationC.txt', sep=' ',quiet=TRUE);\n";	 
	minimaR << "B <- matrix(data=b,ncol=numColumns,byrow=TRUE);\n";
	minimaR << "output <- file(\"minima.txt\",\"w\");\n";
	minimaR << "for ( i in 1:nrow(B) )\n";
	minimaR << "{\n";
	minimaR << "   problem.targetFunction <- B[i,];\n";
	minimaR << "   MIN <- lp(\"min\", problem.targetFunction, problem.leftHandSide, problem.sign, problem.rightHandSide);\n";
	minimaR << "   if ( MIN$status == 0 )\n";
	minimaR << "   {\n";
	minimaR << "      write(\"0\",file=output);\n";
	minimaR << "   }\n";
	minimaR << "   else\n";
	minimaR << "   {\n";
	minimaR << "      write(\"-inf\",file=output);\n";
	minimaR << "   }\n";
	minimaR << "}\n";
	minimaR << "close(output);\n";
	minimaR << "quit();";
	close(minimaR);
		
	run "R --no-save < launcher.R > log.txt";
	run "rm launcher.R log.txt";
    )
    else
    (
   	error "unkwown LP option";    
    );
    
    M := lines get (currentDirectory() | "/minima.txt");
    run "rm minima.txt";
    run "rm -r temp";
    return number(M, x -> x == "-inf");
)


indexOfContainmentLinearForms = method(TypicalValue => List, Options=>{LP=>polymake})

indexOfContainmentLinearForms (List,List) := opts -> (F,C) -> (
    
    R := ring(C#0);
    
    makeDirectory(currentDirectory() | "temp");
    FconeFile := openOut(currentDirectory() | "temp/HrepresentationF.txt");
    CconeFile := openOut(currentDirectory() | "temp/HrepresentationC.txt");
    if opts.LP == polymake then
    (
	for f in F do
    	(
	    FconeFile << "0";
	    for g in gens R do FconeFile << " " | toString(leadCoefficient(f//g));
	    FconeFile << "\n";	
	);
        close(FconeFile);
        for c in C do
    	(
	    CconeFile << "0";
	    for g in gens R do CconeFile << " " | toString(leadCoefficient(c//g));
	    CconeFile << "\n";	
	);
        close(CconeFile);
	
        minimaPolymake := openOut(currentDirectory() | "/launcher.txt");
	minimaPolymake << "use application 'polytope';\n";
        minimaPolymake << "use vars '$Fnef', '$V', '$L';\n";
        minimaPolymake << "open(INPUT,\"< " | "temp/HrepresentationF.txt\");\n";
        minimaPolymake << "$Fnef = new Polytope<Rational>(INEQUALITIES=>new Matrix<Rational>(<INPUT>));\n";
	minimaPolymake << "close(INPUT);\n";
       	minimaPolymake << "open(INPUT,\"< " | "temp/HrepresentationC.txt\");\n";
        minimaPolymake << "open(OUTPUT,\"> " | "minima.txt\");\n";
	minimaPolymake << "while(<INPUT>) {\n";
	minimaPolymake << "  $V = new Vector<Rational>($_);\n";
	minimaPolymake << "  $L = $Fnef->LP(LINEAR_OBJECTIVE=>$V);\n";
	minimaPolymake << "  print OUTPUT $L->MINIMAL_VALUE;\n";
	minimaPolymake << "  print OUTPUT \"\\n\";\n";
	minimaPolymake << "}\n";
	minimaPolymake << "close(INPUT);\n";
	minimaPolymake << "close(OUTPUT);\n";
        minimaPolymake << "exit;";
	close(minimaPolymake);
		
	run "polymake --script launcher.txt > log.txt";
	run "rm launcher.txt log.txt";
    )
    else if opts.LP == lpSolve then
    (
	for f in F do
    	(
	    beginRow := true;
	    for g in gens R do
	    (
	       if beginRow then beginRow = false else FconeFile << " ";
	       FconeFile << toString(leadCoefficient(f//g)) | " " | toString(-leadCoefficient(f//g));
	    );
	    FconeFile << "\n";	
	);
        close(FconeFile);
        for c in C do
    	(
	    beginRow := true;
	    for g in gens R do
	    (
	       if beginRow then beginRow = false else CconeFile << " ";
	       CconeFile << toString(leadCoefficient(c//g)) | " " | toString(-leadCoefficient(c//g));
	    );
	    CconeFile << "\n";	
	);
        close(CconeFile);
	
	minimaR := openOut(currentDirectory() | "/launcher.R");
	minimaR << "rm(list=ls())\nlibrary(lpSolve);\n";
	minimaR << "numColumns <- " | toString(2*(numgens R)) | ";\n";
	minimaR << "a <- scan('temp/HrepresentationF.txt', sep=' ',quiet=TRUE);\n";	 
	minimaR << "problem.leftHandSide <- matrix(data=a,ncol=numColumns,byrow=TRUE);\n";
	minimaR << "numRows <- nrow(problem.leftHandSide);\n";
	minimaR << "problem.sign <- character(numRows);\n";
	minimaR << "for (i in 1:numRows) {problem.sign[i] = \">=\";}\n";
	minimaR << "problem.rightHandSide <- numeric(numRows);\n";	 
	minimaR << "b <- scan('temp/HrepresentationC.txt', sep=' ',quiet=TRUE);\n";	 
	minimaR << "B <- matrix(data=b,ncol=numColumns,byrow=TRUE);\n";
	minimaR << "output <- file(\"minima.txt\",\"w\");\n";
	minimaR << "for ( i in 1:nrow(B) )\n";
	minimaR << "{\n";
	minimaR << "   problem.targetFunction <- B[i,];\n";
	minimaR << "   MIN <- lp(\"min\", problem.targetFunction, problem.leftHandSide, problem.sign, problem.rightHandSide);\n";
	minimaR << "   if ( MIN$status == 0 )\n";
	minimaR << "   {\n";
	minimaR << "      write(\"0\",file=output);\n";
	minimaR << "   }\n";
	minimaR << "   else\n";
	minimaR << "   {\n";
	minimaR << "      write(\"-inf\",file=output);\n";
	minimaR << "   }\n";
	minimaR << "}\n";
	minimaR << "close(output);\n";
	minimaR << "quit();";
	close(minimaR);
		
	run "R --no-save < launcher.R > log.txt";
	run "rm launcher.R log.txt";
    )
    else
    (
   	error "unkwown LP option";    
    );
    
    M := lines get (currentDirectory() | "/minima.txt");
    run "rm minima.txt";
    run "rm -r temp";
    negativePositions := positions(M, x -> x == "-inf");
    return for i in negativePositions list C#i;
)


----------------------------------------------------------------------------------------------------
----------   H-REPRESENTATION FROM V-REPRESENTATION                                       ----------
----------------------------------------------------------------------------------------------------

Vrepresentation2Hrepresentation = method(TypicalValue=>List)

Vrepresentation2Hrepresentation (List,Ring) := (C,S) -> (
 
    R := ring C#0;
    makeDirectory(currentDirectory() | "temp");
    VrepresentationFile := openOut(currentDirectory() | "temp/VrepresentationC.txt");
    for c in C do
    (
    	VrepresentationFile << "0";
	for g in gens R do VrepresentationFile << " " | toString(leadCoefficient(c//g));
	VrepresentationFile << "\n";	
    );
    close(VrepresentationFile);

    commands := openOut(currentDirectory() | "V2H.txt");
    commands << "use application 'polytope';\n";
    commands << "use vars '$C';\n"; 
    commands << "open(INPUT,\"< temp/VrepresentationC.txt\");\n";
    commands << "$C = new Cone<Rational>(INPUT_RAYS=>new Matrix<Rational>(<INPUT>));\n";
    commands << "close(INPUT);\n";
    commands << "open(OUTPUT,\"> temp/HrepresentationC.txt\");\n";
    commands << "print OUTPUT $C->FACETS;\n";
    commands << "close(OUTPUT);\n";
    commands << "exit();\n";
    close(commands);
    
    run "polymake --script V2H.txt > logV2H.txt";
    run "rm V2H.txt logV2H.txt";
    
    L := lines get (currentDirectory() | "temp/HrepresentationC.txt");
    output := {};
    for l in L do
    (
       	t := value replace(" ",",","{"|l|"}");
	t = (1/gcd t)*t;
       	output = output | {sum(for i from 1 to #t-1 list t#i*S_(i-1))};
    );
    run "rm -r temp";  
    return output;   
)

----------------------------------------------------------------------------------------------------
----------   EVALUATE                                                                     ----------
----------------------------------------------------------------------------------------------------
evaluate = method (TypicalValue=>QQ)

evaluate (RingElement,RingElement) := (e,v) -> (
   R := ring e;
   S := ring v;
       
   return sum(for i from 0 to numgens R-1 list lift(leadCoefficient(e//R_i),QQ)*lift(leadCoefficient(v//S_i),QQ)); 
)



----- Unexported methods

complementarySubset = method(TypicalValue=>List);
complementarySubset (List,ZZ) := (L,n) -> (
    output := {};
    for i from 1 to n do if not member(i,L) then output = output | {i};
    return output;
) 

fourPartitions = method(TypicalValue=>List)
fourPartitions ZZ := n -> (
    P := for i from 1 to n list i;
    subdivisions := {};  
    for k1 from ceiling toRR (n/4) to n-3 do
    (
    	T1 := sort subsets(P,k1);
     	for t1 in T1 do 
     	(
	    P1 := select(P,x -> not member(x,t1));
	    n1 := #P1;
	    for k2 from ceiling toRR (n1/3) to min(n1-2,k1) do 
	    (
	   	T2 := sort subsets(P1,k2);
	   	for t2 in T2 do
	   	(
	      	    P2 := select(P1,x -> not member(x,t2));
	      	    n2 := #P2;
	      	    for k3 from ceiling toRR (n2/2) to min(n2-1,k2) do
	      	    (
		 	T3 := subsets(P2,k3);
		 	for t3 in T3 do
		 	(
		    	    t4 := select(P2,x -> not member(x,t3));
		    	    if #t4 <= #t3 then
		    	    ( 
				current := sort {t1,t2,t3,t4};
				if not member(current,subdivisions) then subdivisions = append(subdivisions,current);
		    	    );
		 	);
	      	    );
	   	);
	    );	 
     	); 
    );
    return subdivisions;
) 

subspaceEquations = method(TypicalValue=>List);
subspaceEquations (Ring,List) := (S,L) -> (
   
   R := ring L#0;
   J := trim ideal(for l in L list sum(for i from 0 to numgens S-1 list S_i*lift(leadCoefficient(l//R_i),QQ)));
   inJ := rsort flatten entries gens trim ideal leadTerm J;
   red := for g in gens S list g%J;
   output := {};
   for g in gens S do
   (
      if not member(g,inJ) then output = output | {for r in red list lift(leadCoefficient(r//g),QQ)};    
   );
   return for c in output list sum (for i from 0 to numgens S-1 list c#i*S_i);    
)

subspaceEquations (ZZ,List) := (n,L) -> (
   
   R := ring L#0;
   I := setOfIndices n;
   w := local w;
   S := QQ[for i in I list w_i];
   return subspaceEquations(S,L);
)

subspaceEquations (List) := (L) -> (
   
   R := ring L#0;
   x := local x;
   S := QQ[for i from 0 to numgens R - 1 list x_i];
   return subspaceEquations(S,L);   
)