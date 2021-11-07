newPackage("GroebnerFanHilbertScheme",
           Version => "1.0",
	   Date => "February 2020",
           Authors => {
	               {Name => "Paolo Lella", Email => "paolo.lella@polimi.it", HomePage => "http://www.paololella.it/"}
    	              },
	   Headline => "Ancillary package to the paper \"The Gröbner fan of the Hilbert scheme\"",
	   PackageImports => {"gfanInterface","Truncations","StronglyStableIdeals","Polyhedra"}
	  )

export {
      -- methods
      "compareBorel",
      "compareSetsOfMonomials",
      "minVar",
      "maxVar",
      "borelAdjacent",
      "borelAdjacentIdeals",
      "borelGraph",
      "degenerationGraph",
      "adjacencyMatrix",
      "groebnerFan",
      "termOrder2weightOrder",
      "spanningTree",
      "maximalElementsDegenerationGraph",
      "findCloserVertex",
      "findPathToRoot",
      "findShortestPath",
      "borelGraphDistance",
      "borelGraphDistanceMatrix",
      "maximalElements",
      "minimalElements",
      "segmentCone",
      "maximalityCone",
      "isIrregular",
      "lowerBoundNumberIrreducibleComponents",
      -- options
      "Conjecture"
       }


compareBorel = method(TypicalValue=>ZZ)
compareBorel (RingElement,RingElement) := (m1,m2) -> (
    -- Assume m1, m2 monomials of the same degree
    if m1 == m2 then return 0;
    R := ring m1;
    n := numgens R - 1;
    differenceExponents := for i from 0 to n-1 list sum( for j from 0 to i list degree(R_j,m1)-degree(R_j,m2));
    if min differenceExponents < 0 and max differenceExponents <= 0 then return -1;
    if min differenceExponents >= 0 and max differenceExponents > 0 then return 1;
    return  null;
)

compareSetsOfMonomials = method(TypicalValue=>ZZ,Options=>{MonomialOrder=>GRevLex})
compareSetsOfMonomials (List,List) := opts -> (A,B) -> (
    R := ring first A;
    S := newRing(R,MonomialOrder=>opts.MonomialOrder);
    Aord := rsort for a in A list sub(a,S);
    Bord := rsort for b in B list sub(b,S);
    rel := {};
    for i from 0 to #Aord-1 do
    (
    	if Aord#i == Bord#i then
	(
	    rel = append(rel,0);    
	)
    	else if Aord#i > Bord#i then
	(
	    rel = append(rel,1);    
	)
    	else
	(
	    rel = append(rel,-1);    
	)	
    );
    m := min rel;
    M := max rel;
    if m == 0 and M == 0 then return 0;
    if m < 0 and M == 0 then return -1;
    if m == 0 and M > 0 then return 1;
    return null;
)

compareSetsOfMonomials (Ideal,Ideal) := opts -> (I,J) -> (
    r := gotzmannNumber hilbertPolynomial I;
    Ifrak := flatten entries gens truncate(r,I);
    Jfrak := flatten entries gens truncate(r,J);

    return compareSetsOfMonomials(Ifrak,Jfrak,MonomialOrder=>opts.MonomialOrder);
)

minVar = method(TypicalValue=>RingElement)
minVar (RingElement) := (m) -> (
    -- Assume m a monomial
    R := ring m;
    j := numgens R - 1;
    while j >= 0 and degree(R_j,m) == 0 do j = j-1;
    if j >= 0 then return R_j;
)

maxVar = method(TypicalValue=>RingElement)
maxVar (RingElement) := (m) -> (
    -- Assume m a monomial
    R := ring m;
    j := 0;
    while j < numgens R and degree(R_j,m) == 0 do j = j+1;
    if j < numgens R then return R_j;
)

borelGraph = method(TypicalValue=>Sequence)
borelGraph (ProjectiveHilbertPolynomial,PolynomialRing) := (hp,R) -> (
    r := gotzmannNumber hp;
    V := stronglyStableIdeals(hp,R);
    E := {};
    for i from 0 to #V-2 do
    (
    	for j from i+1 to #V-1 do
	(
	    adjacent := borelAdjacentWithMaxima(V#i,V#j,r);
	    if class adjacent === Sequence then E = append(E,{(i,j),(adjacent#1,adjacent#2)});  
	);      
    );
    return (V,E);
) 

borelGraph (ProjectiveHilbertPolynomial,ZZ) := (hp,n) ->
(
  R := QQ[Variables=>n+1];
  return borelGraph(hp,R);  
);

borelAdjacent = method(TypicalValue=>Boolean)
borelAdjacent (Ideal,Ideal,ZZ) := (J,J',r) -> (
    -- Assume J and J' have the same Hilbert polynomial with Gotzmann number r
    Jr := flatten entries gens truncate(r,J);
    Jr' := flatten entries gens truncate(r,J');
    
    A := rsort select(Jr, x -> not member(x,Jr'));
    maxA := max A;
    for a in A do if compareBorel(maxA,a) === null then return false;

    B := rsort select(Jr', x -> not member(x,Jr));
    maxB := max B;
    for b in B do if compareBorel(maxB,b) === null then return false;

    movesA := for a in A list a/maxA;
    movesB := for b in B list b/maxB;
    return movesA == movesB;
)

borelAdjacent (Ideal,Ideal) := (J,J') -> (
    -- Assume J and J' have the same Hilbert polynomial
    r := gotzmannNumber hilbertPolynomial J;
    return borelAdjacent(J,J',r);
)

borelAdjacentIdeals = method(TypicalValue=>List)
borelAdjacentIdeals Ideal := J -> (
    return borelAdjacentIdeals(J,gotzmannNumber hilbertPolynomial J);
)
    
borelAdjacentIdeals (Ideal,ZZ) := (J,r) -> (
    R := ring J;
    n := numgens R - 1;
    JJ := flatten entries gens truncate(r,J);
    compJJ := select(flatten entries basis(r,R), x -> not member(x,JJ));
    maximal := maximalElements compJJ;
    output := {};
    for M in maximal do
    (
    	minimal := minimalElements select(JJ, m -> minVar m >= minVar M);
	minimal = select(minimal, m -> compareBorel(M,m) === null);
	for m in minimal do
	(
	    E := {};
	    F := {};
	    for b in JJ do
	    (		    
	    	if (c := compareBorel(m,b)) =!= null and c >= 0 then E = append(E,b);
	    );
    	    admissibleAndMaximal := true;
    	    for e in E when admissibleAndMaximal do
	    (
	    	f := (M*e)//m;
	    	admissibleAndMaximal = (f != 0_R);
	    	if admissibleAndMaximal then
	    	(
		    F = append(F,f);
		    for l from 1 to n do
		    (
		    	if degree(R_l,f) > 0 then
		    	(
			    upf := (R_(l-1)*f)//R_l;
		    	    admissibleAndMaximal = member(upf,F) or member(upf,JJ);
		    	);    
		    );
	    	);  
	    );
    	    if admissibleAndMaximal then
	    (
	    	JJ' := JJ;
	    	for e in E do JJ' = delete(e,JJ');
	    	JJ' = JJ' | F;
    	    	output = append(output, saturate ideal JJ');
	    );    
	);	
    );
    return output;
)

degenerationGraph = method(TypicalValue=>Sequence,Options=>{MonomialOrder=>null})
degenerationGraph (ProjectiveHilbertPolynomial,PolynomialRing) := opts -> (hp,R) -> (
    (E,V) := borelGraph(hp,R);
    
    return degenerationGraph(E,V,MonomialOrder=>opts.MonomialOrder);
)

degenerationGraph (ProjectiveHilbertPolynomial,ZZ) := opts -> (hp,n) -> (
    (E,V) := borelGraph(hp,n);
    
    return degenerationGraph(E,V,MonomialOrder=>opts.MonomialOrder);
)

degenerationGraph (List,List) := opts -> (V,E) -> (
    R := ring first V;
    local evaluate;
    if opts.MonomialOrder === null then
    (
    	evaluate = map(R,R);	
    )
    else
    (
    	S := newRing(R,MonomialOrder=>opts.MonomialOrder);
	evaluate = map(S,R);	
    );
    Eo := {};
    for e in E do
    (
    	if (evaluate e#1#0) > (evaluate	e#1#1) then
	(
	    Eo = append(Eo,e | {1});    
	)
    	else
	(
	    Eo = append(Eo,e | {-1});    	    
	);
    );
    return (V,Eo);    
)

degenerationGraph (ProjectiveHilbertPolynomial,PolynomialRing,List) := opts -> (hp,R,omega) -> (
    (E,V) := borelGraph(hp,R);
    
    return degenerationGraph(E,V,omega);
)

degenerationGraph (ProjectiveHilbertPolynomial,ZZ,List) := opts -> (hp,n,omega) -> (
    (E,V) := borelGraph(hp,n);
    
    return degenerationGraph(E,V,omega);
)

degenerationGraph (List,List,List) := opts -> (V,E,omega) -> (
    Eo := {};
    for e in E do
    (
    	if weight(e#1#0,omega) == weight(e#1#1,omega) then
	(
	    Eo = append(Eo,e | {0});    
	)
    	else if weight(e#1#0,omega) > weight(e#1#1,omega) then
	(
	    Eo = append(Eo,e | {1});    	    
	)
    	else
	(
	    Eo = append(Eo,e | {-1});    	    
	);
    );
    return (V,Eo);    
)

degenerationGraph (ProjectiveHilbertPolynomial,ZZ,Cone) := opts -> (hp,n,C) -> (
    (E,V) := borelGraph(hp,n);
    
    return degenerationGraph(E,V,C);
)

degenerationGraph (List,List,Cone) := opts -> (V,E,C) -> (

    return degenerationGraph(V,E, sum entries transpose rays C);    
)

adjacencyMatrix = method(TypicalValue=>Matrix)
adjacencyMatrix (List,List) := (V,E) -> (
    M := mutableMatrix(ZZ,#V,#V); 
    if #(E#0) == 2 then
    (
    	for e in E do
    	(
	    M_(e#0#0,e#0#1) = 1;
	    M_(e#0#1,e#0#0) = 1;
    	);
    )
    else
    (
    	for e in E do
    	(
	    M_(e#0#0,e#0#1) = -1*e#2;
	    M_(e#0#1,e#0#0) = e#2;
    	);		
    );
    return matrix M;
)

groebnerFan = method(TypicalValue=>Sequence)
groebnerFan (ProjectiveHilbertPolynomial,ZZ) := (hp,n) -> (
    (V,E) := borelGraph(hp,n);
    return groebnerFan(V,E);     
)

groebnerFan (ProjectiveHilbertPolynomial,PolynomialRing) := (hp,R) -> (
    (V,E) := borelGraph(hp,R);
    return groebnerFan(V,E);     
)

groebnerFan (List,List) := (V,E) -> (
    R := ring first V;
    S := newRing(R,MonomialOrder=>GLex);
    n := numgens R;
    fromRtoS := map(S,R);
    boundary := for i from 0 to n-2 list for j from 0 to n-1 list if j == i then 1 else if j == i+1 then -1 else 0;
    boundary = boundary | {(for i from 0 to n-2 list 0) | {1}};
    equations := {};
    sinkOrder := {};
    for e in E do
    (
	equations = append (equations,for i from 0 to n-1 list degree(R_i,e#1#0)-degree(R_i,e#1#1));
     	if (fromRtoS e#1#0) > (fromRtoS e#1#1) then sinkOrder = append(sinkOrder,1) else sinkOrder = append(sinkOrder,-1);
    );

    queue := {sinkOrder};
    extremalRays := {};
    maximalCones := {};
    visited := {};
    while #queue > 0 do
    (
	edgeOrder := first queue;
	queue = delete(edgeOrder,queue);
	visited = append(visited,edgeOrder);
	currentCone := coneFromHData matrix (boundary | for i from 0 to #equations-1 list edgeOrder#i*equations#i);	
	currentFacets := facets currentCone;
	currentRays := entries transpose rays currentCone;
    	newMaximalCone := {};
	for r in currentRays do
	(
	    p := position(extremalRays, x-> x == r);
	    if p === null then
	    (
	    	newMaximalCone = append(newMaximalCone,#extremalRays);
		extremalRays = append(extremalRays,r);
	    )
	    else
	    (
	    	newMaximalCone = append(newMaximalCone,p);
	    );   
	);    
    	maximalCones = append(maximalCones,sort newMaximalCone);

	for i from 0 to numRows currentFacets - 1 do
	(
	    currentFacet := flatten entries currentFacets^{i};
	    if not member(currentFacet,boundary) then
	    ( 
		isFlippable := true;
    	    	newOrder := {};
		j := 0;
		while j < #E and isFlippable do
		(
		    if rank matrix {currentFacet,equations#j} == 1 then
		    (
		    	newOrder = append(newOrder,-1*edgeOrder#j);	
			if edgeOrder#j == 1 then
			(
			    isFlippable = (fromRtoS E#j#1#0) > (fromRtoS E#j#1#1);
			)
		        else
			(
			    isFlippable = (fromRtoS E#j#1#0) < (fromRtoS E#j#1#1);
			);	
		    )
		    else
		    (
		    	newOrder = append(newOrder,edgeOrder#j);	
		    );  
		    j = j+1;  
		);
	    	if isFlippable and not member(newOrder,visited) then
		(
		    queue = append(queue,newOrder);
		);	       
	    ); 
	); 		
    );
    return (V,E,fan(transpose matrix extremalRays,maximalCones));   
)

termOrder2weightOrder = method(TypicalValue => List)
termOrder2weightOrder (List,Matrix) := (E,M) -> (
    R := ring E#0#1#0;
    n := numgens R - 1;
    EE := new MutableList from for i from 0 to n list {};
    for e in E do
    (
    	v := transpose matrix { for i from 0 to n list degree(R_i,e#1#0) - degree(R_i,e#1#1)};	
	i := 0;
	while M^{i}*v == 0 do i=i+1;
	EE#i = append(EE#i,v);
    );
    XX := new MutableList from for i from 0 to n list {};
    for k from 0 to n-1 do
    (
    	i := 0;
	while M_(i,k) - M_(i,k+1) == 0 do i=i+1;
	XX#i = append(XX#i,k);
    );
    
    firstNonZero := true;
    L := new MutableList from for i from 0 to n list 0;
    i := n;
    while i > 0 do
    (
    	if #(EE#i) != 0 or #(XX#i) != 0 then
	(
	    if firstNonZero then
	    (
	    	L#i = 1;
		firstNonZero = false;	
	    )
	    else
	    (
	    	if #(EE#i) == 0 then
		(
    	    	    L#i = 1 + max for k in XX#i list -sum(for j from i+1 to n list L#j*(M_(j,k)-M_(j,k+1)))/(M_(i,k)-M_(i,k+1));
		)
	    	else if #(XX#i) == 0 then
		(
    	    	    L#i = 1 + max for v in EE#i list -sum(for j from i+1 to n list L#j*(M^{j}*v)_(0,0))/(M^{i}*v)_(0,0);		    
		)
	    	else
		(
		    L1 := max for k in XX#i list -sum(for j from i+1 to n list L#j*(M_(j,k)-M_(j,k+1)))/(M_(i,k)-M_(i,k+1));
    	    	    L2 := max for v in EE#i list -sum(for j from i+1 to n list L#j*(M^{j}*v)_(0,0))/(M^{i}*v)_(0,0);		    
    	    	    L#i = 1 + max(L1,L2);
		);	
	    );     
	);
    	i = i-1;
    );
    W := for j from 0 to n list sum (for i from 0 to n list L#i*M_(i,j));
    if (m := min W) <= 0 then W = for w in W list w + 1 - m; 
    return W;
)

spanningTree = method(TypicalValue=>List,Options=>{MonomialOrder=>GLex})
spanningTree (List) := opts -> (V) -> (
    R := ring first V;
    hp := hilbertPolynomial first V;
    L := lexIdeal(hp,R);
    return spanningTree(V,L,MonomialOrder=>GLex);
)

spanningTree (List,Ideal) := opts -> (V,hilbSegment) -> (
    R := ring first V;
    n := numgens R - 1;
    S := newRing(R,MonomialOrder=>opts.MonomialOrder);
    fromRtoS := map(S,R);
    fromStoR := map(R,S);
    L := fromRtoS(hilbSegment);
    r := gotzmannNumber hilbertPolynomial L;
    LL := rsort flatten entries gens truncate (r,L);
    SS := rsort flatten entries basis(r,S);
    tree := {};
    for j from 0 to #V-1 do 
    (
	J := fromRtoS(V#j);
    	if J != L then
	(
	    JJ := rsort flatten entries gens truncate (r,J);
	    -- Step 0
	    A := select(LL, x -> not member(x,JJ));
	    B := select(JJ, x -> not member(x,LL));
	    father := false;
	    while not father do 
	    (
		-- Step 1
		a := max A;
	    	k := minVar a;
	    	b := min select(B, x -> minVar x == k);
	    	E := {};
		F := {};
		-- Step 2
		for m in B do
		(		    
    		    if (c := compareBorel(b,m)) =!= null and c >= 0 then E = append(E,m);
		);
	    	admissibleAndMaximal := true;
	    	for e in E when admissibleAndMaximal do
		(
		    f := (a*e)//b;
		    admissibleAndMaximal = (f != 0_S);
		    if admissibleAndMaximal then
		    (
			F = append(F,f);
			for l from 1 to n do
			(
			    if degree(S_l,f) > 0 then
			    (
				upf := (S_(l-1)*f)//S_l;
			    	admissibleAndMaximal = member(upf,F) or member(upf,JJ);
			    );    
			);
		    );  
		);
	    	if admissibleAndMaximal then
		(
		    father = true;
		    JJ' := JJ;
		    for e in E do JJ' = delete(e,JJ');
		    JJ' = JJ' | F;
		    J' := fromStoR saturate ideal JJ';
		    i := position(V, x-> x == J');
		    if i < j then
		    (
		    	tree = append(tree,{(i,j),(a,b),1});
		    )
		    else
		    (
		    	tree = append(tree,{(j,i),(b,a),-1});
		    );
		)
	    	else
		(
		    -- Step 3
		    A = select (A, x-> compareBorel(a,x) === null);
		);
	    	
	    );	    
	);    
    );
    return tree;
)

findCloserVertex = method(TypicalValue=>Ideal,Options=>{MonomialOrder=>GLex})
findCloserVertex (Ideal) := opts -> (J) -> (
    R := ring J;
    hp := hilbertPolynomial J;
    L := lexIdeal(hp,R);
    return findCloserVertex(J,L,MonomialOrder=>GLex);
)

findCloserVertex (Ideal,Ideal) := opts -> (I,hilbSegment) -> (
    R := ring I;
    n := numgens R - 1;
    S := newRing(R,MonomialOrder=>opts.MonomialOrder);
    L := sub(hilbSegment,S);
    r := gotzmannNumber hilbertPolynomial L;
    LL := rsort flatten entries gens truncate (r,L);
    SS := rsort flatten entries basis(r,S);
    J := sub(I,S);
    JJ := rsort flatten entries gens truncate (r,J);
    -- Step 0
    A := select(LL, x -> not member(x,JJ));
    B := select(JJ, x -> not member(x,LL));
    father := false;
    while not father do 
    (
	-- Step 1
	a := max A;
    	k := minVar a;
    	b := min select(B, x -> minVar x == k);
    	E := {};
	F := {};
	-- Step 2
	for m in B do
	(		    
	    if (c := compareBorel(b,m)) =!= null and c >= 0 then E = append(E,m);
	);
    	admissibleAndMaximal := true;
    	for e in E when admissibleAndMaximal do
	(
	    f := (a*e)//b;
	    admissibleAndMaximal = (f != 0_S);
	    if admissibleAndMaximal then
	    (
		F = append(F,f);
		for l from 1 to n do
		(
		    if degree(S_l,f) > 0 then
		    (
			upf := (S_(l-1)*f)//S_l;
		    	admissibleAndMaximal = member(upf,F) or member(upf,JJ);
		    );    
		);
	    );  
	);
    	if admissibleAndMaximal then
	(
	    father = true;
	    JJ' := JJ;
	    for e in E do JJ' = delete(e,JJ');
	    JJ' = JJ' | F;
    	    return sub( saturate ideal JJ',R);
	)
    	else
	(
	    -- Step 3
	    A = select (A, x-> compareBorel(a,x) === null);
	);  	
    );	    
)   

findPathToRoot= method(TypicalValue=>List,Options=>{MonomialOrder=>GLex})
findPathToRoot (Ideal) := opts -> (J) -> (
    R := ring J;
    hp := hilbertPolynomial J;
    L := lexIdeal(hp,R);
    return findPathToRoot(J,L,MonomialOrder=>GLex);
)

findPathToRoot (Ideal,Ideal) := opts -> (J,hilbSegment) -> (
    pathToRoot := {J};
    while pathToRoot#-1 != hilbSegment do
    (
    	pathToRoot = append(pathToRoot,findCloserVertex(pathToRoot#-1,hilbSegment,MonomialOrder=>opts.MonomialOrder));
    );
    return pathToRoot;
)

findShortestPath = method(TypicalValue=>List)
findShortestPath (Ideal,Ideal) := (J,I) -> (
    (V,E) := borelGraph(hilbertPolynomial J,ring J);
    
    return findShortestPath(J,I,V,E);
)

findShortestPath (Ideal,Ideal,List,List) := (J,I,V,E) -> (
    j := position(V, x -> x == J);
    i := position(V, x -> x == I);
    
    return findShortestPath(j,i,V,E);
)

findShortestPath (ZZ,ZZ,List,List) := (j,i,V,E) -> (
    queue := {{j}};
    while true do
    (
    	currentPath := first queue;
	queue = delete(currentPath,queue);
	lastIndex := currentPath#-1;
	firstPart := for i from 0 to #currentPath-2 list currentPath#i;
	if lastIndex == i then return for k in currentPath list V#k;
	
	edges := select(E, e -> e#0#0 == lastIndex and not member(e#0#1,firstPart));
	for e in edges do queue = append(queue,currentPath | {e#0#1});
	
	edges = select(E, e -> e#0#1 == lastIndex and not member(e#0#0,firstPart));
    	for e in edges do queue = append(queue,currentPath | {e#0#0});
    );    
)

maximalElementsDegenerationGraph = method(TypicalValue=>List)
maximalElementsDegenerationGraph (List,List) := (V,E) -> (
    A := adjacencyMatrix(V,E);
    output := {};
    for i from 0 to numColumns A-1 do
    (
    	if min flatten entries A_{i} == 0 then output = append(output,V#i);	
    );
    return output;
)

borelGraphDistanceMatrix = method(TypicalValue=>Matrix)
borelGraphDistanceMatrix (ProjectiveHilbertPolynomial,ZZ) := (hp,n) -> (
    (V,E) := borelGraph(hp,n);
    return borelGraphDistanceMatrix(V,E);     
)

borelGraphDistanceMatrix (ProjectiveHilbertPolynomial,PolynomialRing) := (hp,R) -> (
    (V,E) := borelGraph(hp,R);
    return borelGraphDistanceMatrix(V,E);     
)

borelGraphDistanceMatrix (List,List) := (V,E) -> (
    A := adjacencyMatrix(V,E);
    D := mutableMatrix A;
    d := 1;
    Ad := A;
    while min flatten entries Ad == 0 do
    (
    	Ad = Ad*A;
	d = d+1;
	for i from 0 to #V-2 do
	(
	    for j from i+1 to #V-1 do
	    (
		if Ad_(i,j) != 0 and D_(i,j) == 0 then (D_(i,j) = d; D_(j,i) = d;);
	    );    
	);
    );
    return matrix D;
)

borelGraphDistance = method(TypicalValue=>ZZ)
borelGraphDistance (ZZ,ZZ,List,List) := (j,i,V,E) -> (   
    return length findShortestPath(j,i,V,E) - 1;    
)

borelGraphDistance (Ideal,Ideal,List,List) := (J,I,V,E) -> (
    return length findShortestPath(J,I,V,E) - 1;   
)

borelGraphDistance (Ideal,Ideal) := (J,I) -> (
    return length findShortestPath(J,I) - 1;   
)

minimalElements = method(TypicalValue=>List)
minimalElements (List) := (B) -> (
    if #B > 0 then
    (
    	R := ring B#0;
    	n := numgens R-1;
    	output := {};
    	for m in B do
    	(
	    isMinimal := true;
	    i := 0;
    	    while isMinimal and i < n do
	    (
	    	if degree(R_i,m) > 0 then isMinimal = not member((m*R_(i+1))//R_i,B);	
     	    	i = i+1;
	    );
	
	    if isMinimal then output = append(output,m);	
    	);
        return output;
    )
    else
    (
    	return {};	
    );
)

maximalElements = method(TypicalValue=>List)
maximalElements (List) := (B) -> (
    if #B > 0 then
    (
	R := ring B#0;
    	n := numgens R-1;
    	output := {};
    	for m in B do
    	(
	    isMaximal := true;
	    i := n;
    	    while isMaximal and i > 0 do
	    (
	    	if degree(R_i,m) > 0 then isMaximal = not member((m*R_(i-1))//R_i,B);	
     	    	i = i-1;
		);
	
	        if isMaximal then output = append(output,m);	
    	   );
       return output;
    )
    else
    (
    	return {};	
    );
)

segmentCone = method(TypicalValue=>Cone)
segmentCone (Ideal) := J -> (
    return segmentCone(J, gotzmannNumber hilbertPolynomial J);
)

segmentCone (Ideal,ZZ) := (J,r) -> (
    R := ring J;
    n := numgens R - 1;
    JJ := flatten entries gens truncate(r,J);
    compJJ := select(flatten entries basis(r,R), x -> not member(x,JJ));
    mm := minimalElements JJ;
    MM := maximalElements compJJ;
    inequalities := for i from 0 to n-1 list for j from 0 to n list if j == i then 1 else if j == i+1 then -1 else 0;
    inequalities = inequalities | {(for i from 0 to n-1 list 0) | {1}};
    for m in mm do
    (
    	for M in MM do
	(
	     inequalities = append (inequalities,for i from 0 to n list degree(R_i,m)-degree(R_i,M));    
	);	
    );
    C :=  coneFromHData matrix inequalities;
    if dim C == ambDim C then return coneFromHData facets C else return null;
)

maximalityCone = method(TypicalValue=>Cone)
maximalityCone (Ideal,List,List) := (J,V,E) -> (
    R := ring J;
    n := numgens R;
    j := position(V, x -> x == J);
    inequalities := for i from 0 to n-2 list for j from 0 to n-1 list if j == i then 1 else if j == i+1 then -1 else 0;
    inequalities = inequalities | {(for i from 0 to n-2 list 0) | {1}};
    for e in E do
    (
    	if e#0#0 == j then
	(
	    inequalities = append (inequalities,for i from 0 to n-1 list degree(R_i,e#1#0)-degree(R_i,e#1#1));
	)
    	else if e#0#1 ==j then
	(
	    inequalities = append (inequalities,for i from 0 to n-1 list degree(R_i,e#1#1)-degree(R_i,e#1#0));	    
	);	
    );
    C :=  coneFromHData matrix inequalities;
    if dim C == ambDim C then return coneFromHData facets C else return null;
)

isIrregular = method(TypicalValue=>Boolean)
isIrregular (Ideal,List,List,ZZ) := (J,V,E,r) -> (
    maxCone := maximalityCone(J,V,E);
    if maxCone === null then return false;
    
    segCone := segmentCone(J,r);
    if segCone === null then return true;
    
    return maxCone != segCone;    
)

isIrregular (Ideal,List,List) := (J,V,E) -> (
    return isIrregular(J,V,E,gotzmannNumber hilbertPolynomial J);
)

lowerBoundNumberIrreducibleComponents = method(TypicalValue => ZZ,Options=>{Conjecture=>false})

lowerBoundNumberIrreducibleComponents (ProjectiveHilbertPolynomial,PolynomialRing) := (hp,R) -> (
    return lowerBoundNumberIrreducibleComponents groebnerFan(hp,R);
) 

lowerBoundNumberIrreducibleComponents (ProjectiveHilbertPolynomial,ZZ) := (hp,n) ->
(
  R := QQ[Variables=>n+1];
  return lowerBoundNumberIrreducibleComponents(hp,R);  
);

lowerBoundNumberIrreducibleComponents (List,List,Fan) := opts -> (V,E,F) -> (
    raysF := rays F;
    lowerBound := 1;
    for mC in maxCones(F) do
    (
	newMaximalElements := maximalElementsDegenerationGraph degenerationGraph(V,E,coneFromVData raysF_mC);
	if #newMaximalElements > lowerBound then
	(
	    if not opts.Conjecture then
	    (
	    	W := sum entries transpose raysF_mC;
	    	for i from 0 to #newMaximalElements-2 do
		(
		    for j from i+1 to #newMaximalElements-2 do
		    (
			if compareSetsOfMonomials(newMaximalElements#i,newMaximalElements#j,MonomialOrder=>{Weights=>W}) =!= null then
			(
			    print "Counterexample to Conjecture 4.17!";
			    print "Please notify via email to paolo.lella@polimi.it";
			    return null;    
			);
		    );
		);
	    );
	    lowerBound = #newMaximalElements; 
    	);
    );
    return lowerBound;
)

--------------------------------------------------------------------------------
--------        AUXILIARY METHODS
--------------------------------------------------------------------------------

weight = method()
weight (RingElement,List) := (m,w) -> (
    R := ring m;
    return sum(for i from 0 to min(numgens R,#w) - 1 list w#i*degree(R_i,m));    
)

borelAdjacentWithMaxima = method(TypicalValue=>List)
borelAdjacentWithMaxima (Ideal,Ideal,ZZ) := (J,J',r) -> (
    -- Assume J and J' have the same Hilbert polynomial with Gotzmann number r
    Jr := flatten entries gens truncate(r,J);
    Jr' := flatten entries gens truncate(r,J');
    
    A := select(Jr, x -> not member(x,Jr'));
    maxA := max A;
    for a in A do if compareBorel(maxA,a) === null then return false;

    B := select(Jr', x -> not member(x,Jr));
    maxB := max B;
    for b in B do if compareBorel(maxB,b) === null then return false;

    movesA := for a in A list a/maxA;
    movesB := for b in B list b/maxB;
    if movesA == movesB then
    (
	return (true,maxA,maxB);
    )
    else
    (
    	return false;	
    );
)