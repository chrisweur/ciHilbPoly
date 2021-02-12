-*------------------------------------------------------------------------
M2 code to accompany "Complete Intersections of given Hilbert polynomial"

Last updated: 2/12/2021
Author: Christopher Eur

Many thanks to Justin Chen and Mengyuan Zhang for their contributions
-------------------------------------------------------------------------*-



--< ElementarySymmetric >-- 
-* sequence of codes to express a symmetric polynomial into polynomial in
elementary symmetric functions.*-

--Define the ring whose variables are elemenary symmetric functions, and
-- its coefficient ring is the original ring.
symRing = R->(
    n := #gens R;
    w := apply(n,i->1) | toList(1..n);
    return (coefficientRing R)[gens R,e_1..e_n,MonomialOrder=>{Weights => w,Lex}]
)

--Build Grobner basis for leading term elimination to write in elementry symmetrics.
buildSymmetricGB = R -> (
	n := # gens R; 
	S := symRing R;
	xvars := (gens S)_{0..n-1};
	svars := (gens S)_{n..2*n-1};
	A := coefficientRing(R)[svars,xvars][x];
 	xvars = xvars / (i->sub(i,A));
 	svars = svars / (i->sub(i,A));
	g := x^n + sum apply(n, i -> svars_i*x^(n-i-1));
	l := {};
	for i to n-1 do (
	     f :=sub(g,x=>-xvars_(n-i-1));
	     l = append(l,f);
	     g=g//(x+xvars_(n-i-1));
		);
	return l / (i -> sub(i,S));
)

-*Writes a polynomial in terms of elementary symmetric polynomials of its variables *-
elementarySymmetric = method();
elementarySymmetric (RingElement):=  f -> (
	n := numgens ring f;
	I := ideal buildSymmetricGB(ring f);
	forceGB matrix{I_*};
	sub(sub(f,ring I) % I,QQ[(gens ring I)_{n..2*n-1}]) 
)



--< Todd polynomial computation and the tilde-Lambda's>--

--computes the Bernoulli numbers B(n) (following the B^- (minus) convention)
bernoulli := memoize (
     n -> if n === 0 then 1 else - sum(n, i -> binomial(n + 1, i) * bernoulli(i)/(n + 1))
     )

-* Let c(F) = prod_i (1+b_i) where i = 1..r so that m-th elementary symmetric polynomial of the b_i's is c_m.
The following computes the Todd polynomial of F as a polynomial in
the c_m's assuming that the dimension of the variety is n. *-
-- InList => true option gives the Todd classes in a list instead of in a polynomial
-* toCiDeg => true option gives the tilde-Lambda's by converting c_i's into the
complete homogeneous symmetric functions in the degree sequence (a_1,...,a_c)
and then converting the Todd classes into elementary symmetric polynomials. *-
toddPoly = method(Options => {InList => false} )
toddPoly(ZZ,ZZ) := RingElement => opts -> (r,n) -> (
    b := local b;
    t := local t;
    A' := QQ[b_1..b_r,t];
    A := A'/t^(n+1);
    raw := product(r, i -> sum(n+1, j -> (-1)^j*bernoulli(j)*(A_i*(gens A)_(-1))^j/(j!)));
    liftRaw := lift(raw,A');
    A'' := QQ[b_1..b_r][t];
    liftRaw' := (map(A'',A',join(gens coefficientRing A'', gens A''))) liftRaw;
    c := local c; R := QQ[c_1..c_r][t];
    C := apply(n+1, i -> elementarySymmetric coefficient(t^i,liftRaw'));
    toddPol := sum(#C, i -> (map(R, ring C_i, gens coefficientRing R)) C_i * t^i);
    if not opts.InList then return toddPol;
    L := apply(n+1, i -> coefficient(t^i,toddPol))
)


--the characteristic function for Todd classes
ToddCharFct := x -> ((1 - exp(-x))//x)^(-1)

--Alternate code for toddPoly above (same functionality)
--Turns out it's not any faster (actually a bit slower...)
toddPoly2 = method(Options => {InList => false});
toddPoly2(ZZ,ZZ) := List => opts -> (r,n) -> (
    b := local b; t := local t;
    A := QQ[b_1..b_r][t]/t^(n+2);  
    raw := product(r, i -> ToddCharFct((coefficientRing A)_i*A_0)) % t^(n+1);
    C := apply(n+1, i -> elementarySymmetric coefficient(t^i, raw));
    c := local c; R := QQ[c_1..c_r][t];
    toddPol := sum(#C, i -> (map(R, ring C_i, gens coefficientRing R)) C_i * t^i);
    if not opts.InList then return toddPol;
    L := apply(n+1, i -> coefficient(t^i,toddPol))
)



--converts the complete homogeneous symmetric polynomial of degree k into a  polynomial in the 
--elementary symmetric polynomials R = QQ[e_1, ... , e_c]
HtoE = method();
HtoE(ZZ,Ring) := RingElement => (k,R) -> (
    if k == 0 then return 1_R;
    -sum(1..k, i -> (-1)^i * HtoE(k-i,R) * (if i > numgens R then 0_R else R_(i-1)))
)


-* computes the e_c^{-1}*Lambda_i's of a generic complete intersection in P^n of
 codimension c. This is also denoted as tilde Lambda_i *-
ciToddPoly = method();
ciToddPoly(ZZ,ZZ) := List => (c,n) -> (
    e := local e;
    S := QQ[e_1..e_c];
    L := toddPoly(n-c,n-c, InList => true);
    HtoEList := apply(toList(1..(n-c)), i -> (-1)^i*HtoE(i,S)); 
    apply(L, l -> (map(S, ring l, HtoEList))l)
)
--when the ring R = QQ[e_1..e_c] is fixed
ciToddPoly(ZZ,ZZ,Ring) := List => (c,n,R) -> (
    apply(ciToddPoly(c,n), l -> (map(R,ring l, gens R)) l)
)



--< Finding Counter Examples >--

-- elementary symmetric polynomials
elemSymPoly = method()
elemSymPoly(ZZ,List) := (i,L) -> sum(apply(subsets(L,i), s -> product s))

-* Let L be a list and f be a function that can be applied to each element in L.
The output is lists of size>1 consisting of elements sharing the same f-value. *-
fDuplicates = method()
fDuplicates(Function, List) := List => (f,L) -> (
    fTally := new MutableHashTable;
    apply(L, l -> (
	val := f(l);
	if not fTally #? val then fTally#val = {l} else fTally#val = append(fTally#val, l);
	) );
    repeatKeys = select(keys fTally, i -> #(fTally#i)>1);
    fDup := apply(repeatKeys, i -> fTally#i)
)

-*Given a list F of functions that applies to integer sequences of length c,
searches for sequences whose sum is m that agree on the given list of functions. *-
sumFDup = method()
sumFDup(ZZ,ZZ,List) := List => (c,m,F) -> (
    L := {select((partitions(m,c)/conjugate)/toList, l -> length l ==c)};
    i := 0;
    while i < #F do (
	if L == {} then << "none at " << i << return false;
        L = flatten apply(L, l -> fDuplicates(F_i,l));
        i = i+1;
    );
    if L == {} then << "none at " << i << return false else << L << return true;
)

--list of functions used for sumFDup
F3 = {l -> product l}
F4 = {l -> product l, l -> sum(l, i-> i^2)}
F5 = {l -> product l, l -> sum(l, i-> i^2), l -> (elemSymPoly(4,l)) - (sum l)*(elemSymPoly(3,l))}
F6 = {l -> product l, l -> sum(l, i-> i^2), l -> (elemSymPoly(4,l)) - (sum l)*(elemSymPoly(3,l)), l -> (elemSymPoly(3,l))^2 - 2*(elemSymPoly(2,l))*(elemSymPoly(4,l)) + 2*(sum l)*(elemSymPoly(5,l))}
F7 = {l -> product l, l -> sum(l, i-> i^2), l -> (elemSymPoly(4,l)) - (sum l)*(elemSymPoly(3,l)), l -> (elemSymPoly(3,l))^2 - 2*(elemSymPoly(2,l))*(elemSymPoly(4,l)) + 2*(sum l)*(elemSymPoly(5,l)), l -> seqToHilb(l,15)}
FList = {F3,F4,F5,F6,F7}


--searches for a counterexample for c=k starting at sum of sequence ranging from  m to n.
iterSearch = (m,n,k) -> ( 
    i := m; stat := false;
    while m-1 < i and i < n+1 and stat == false do (
    stat = sumFDup(k,i,FList_(k-3));
    print (i, stat);
    collectGarbage();
    i = i+1;
    )
)


--converts a sequence of integers L into hilbert Polynomial of a complete intersection in P^n with
--degree sequence L.
seqToHilb = method()
seqToHilb(List,ZZ) := RingElement => (L,n) -> (
    x := symbol x;
    R := QQ[x_0..x_n];
    I := ideal(apply(#L, i -> R_i^(L_i)));
    hilbertPolynomial I
)    





end


--< computations for tilde-Lambda's >--
restart
load "ciHilbPoly_upload.m2"

-- c=3, n=5 case
ciToddPoly(3,5)
oo/factor
--texMath oo

-- c=4, n=8 case
ciToddPoly(4,8)
oo/factor
-- texMath oo

-- c=5, n=11 case
R = QQ[e_1..e_5];
L = (ciToddPoly(5,11,R))_{0,1,2,4,6}
(L/factor)
R' = QQ[e_1..e_5,K];
L = L/(l -> sub(l,R'))
sub(L_4, R'_3 => R'_0*R'_2+R'_5)
first factor oo

-- c=6, n=14 case
e = symbol e;
R = QQ[e_1..e_6];
L = (ciToddPoly(6,14,R))_{0,1,2,4,6,8}
-- texMath (L/factor)
S = QQ[e_1..e_5,K,K'];
L' = L/(l -> sub(l,S))
L' = apply({4,5}, i -> sub(L'_i, S_3 => S_0*S_2+S_5))
F = sub(L'_1, S_4 => - S_2^2/(2*S_0) + S_1*S_2 + K')
F = numerator F
T = QQ[e_1,e_2,e_4,e_5,K,K'][e_3]
F = sub(F,T)
F' = diff(e_3, F)/3
a = coefficient(e_3^2,F'); b = coefficient(e_3,F'); c = coefficient(e_3^0,F');
a,b,c
D = -(-3*e_3-b/2)^2 + ((b/2)^2 - a*c)
D = sub(D,S)
D = sub(D, {S_5 => -S_0*S_2+S_3, S_6 => S_2^2/(2*S_0) - S_1*S_2 + S_4} )/6
-- texMath oo

--Testing the sign for c=6 case
El := L -> elemSymPoly(1,L) *elemSymPoly(2,L) *elemSymPoly(3,L)-(elemSymPoly(1,L))^2 *elemSymPoly(4,L)-(elemSymPoly(3,L))^2+elemSymPoly(1,L)* elemSymPoly(5,L);
BL = select((partitions(80,6)/conjugate)/toList, l -> length l ==6);
#BL
time BLE = apply(BL, i -> El i); -- 50 seconds
select(BLE, i -> i<0)


--< computations finding the counterexamples >--

restart
load "ciHilbPoly.m2"

iterSearch(4,30,4)
iterSearch(5,70,5)
time iterSearch(146,146,6) -- 180 seconds
-- iterSearch(6,146,6) -- takes about a day or two
-- may need to break the above into different sessions if garbage collector is not working properly


-- c=7, n=17 case
restart
load "ciHilbPoly.m2"
time L = (ciToddPoly(7,17))_{0,1,2,4,6,8,10} -- 211 seconds
e = symbol e; K = symbol K; K' = symbol K';
S = QQ[e_1..e_7,K,K'];
L' = L/(l -> (map(S,ring l,apply(7, i -> S_i)))l)
L' = apply({4,5,6}, i -> sub(L'_i, S_3 => S_0*S_2+S_5))
factor L'_0
L'' = apply(toList(1..2), i -> sub(L'_i, S_4 => - S_2^2/(2*S_0) + S_1*S_2 - 6*S_0*S_5  + 5*S_1*S_5/(2*S_0) + S_5/S_0+ K'))
L''/denominator
S' = QQ[e_1,e_2,e_7,K,K'][e_3,e_6];
(L''/numerator)/(l -> sub(l,S'))
f = value oo_0, g = value oo_1


-* (ciToddPoly(7,17))_{0,1,2,4,6,8,10} saved here:

{1, (1/2)*e_1, (1/6)*e_1^2-(1/12)*e_2,
      (1/120)*e_1^4-(1/80)*e_1^2*e_2+(1/360)*e_2^2-(1/720)*e_1*e_3+(1/720)*e_4,
      (1/5040)*e_1^6-(1/2016)*e_1^4*e_2+(1/2520)*e_1^2*e_2^2-(1/5040)*e_1^3*e_3-(1/20160)*e_2^3+(1
      /20160)*e_1*e_2*e_3+(1/5040)*e_1^2*e_4+(1/60480)*e_3^2-(1/12096)*e_2*e_4+(1/30240)*e_1*e_5-(
      1/30240)*e_6, (1/362880)*e_1^8-(1/103680)*e_1^6*e_2+(1/72576)*e_1^4*e_2^2-(1/145152)*e_1^5*e
      _3-(1/145152)*e_1^2*e_2^3+(1/145152)*e_1^3*e_2*e_3+(1/145152)*e_1^4*e_4+(1/1814400)*e_2^4-(1
      /1209600)*e_1*e_2^2*e_3+(1/403200)*e_1^2*e_3^2-(1/86400)*e_1^2*e_2*e_4+(17/3628800)*e_1^3*e_
      5-(1/1814400)*e_2*e_3^2+(1/518400)*e_2^2*e_4-(1/3628800)*e_1*e_3*e_4-(1/907200)*e_1*e_2*e_5
      -(17/3628800)*e_1^2*e_6+(1/1814400)*e_4^2-(1/1209600)*e_3*e_5+(1/518400)*e_2*e_6-(1/1209600
      )*e_1*e_7, (1/39916800)*e_1^10-(1/8870400)*e_1^8*e_2+(1/4276800)*e_1^6*e_2^2-(1/8553600)*e_1
      ^7*e_3-(1/4561920)*e_1^4*e_2^3+(1/4561920)*e_1^5*e_2*e_3+(1/8553600)*e_1^6*e_4+(1/13305600)*
      e_1^2*e_2^4-(1/8870400)*e_1^3*e_2^2*e_3+(47/479001600)*e_1^4*e_3^2-(181/479001600)*e_1^4*e_2
      *e_4+(19/119750400)*e_1^5*e_5-(1/239500800)*e_2^5+(1/119750400)*e_1*e_2^3*e_3-(19/239500800
      )*e_1^2*e_2*e_3^2+(127/479001600)*e_1^2*e_2^2*e_4-(1/26611200)*e_1^3*e_3*e_4-(73/479001600)*
      e_1^3*e_2*e_5-(19/119750400)*e_1^4*e_6+(1/119750400)*e_2^2*e_3^2-(1/479001600)*e_1*e_3^3-(1/
      39916800)*e_2^3*e_4+(1/95800320)*e_1*e_2*e_3*e_4+(37/479001600)*e_1^2*e_4^2+(1/59875200)*e_1
      *e_2^2*e_5-(29/239500800)*e_1^2*e_3*e_5+(43/159667200)*e_1^2*e_2*e_6-(1/8553600)*e_1^3*e_7+(
      1/479001600)*e_3^2*e_4-(1/47900160)*e_2*e_4^2+(13/479001600)*e_2*e_3*e_5+(1/239500800)*e_1*e
      _4*e_5-(1/22809600)*e_2^2*e_6+(1/239500800)*e_1*e_3*e_6+(13/479001600)*e_1*e_2*e_7+(1/
      95800320)*e_5^2-(1/39916800)*e_4*e_6+(1/47900160)*e_3*e_7}

*-
