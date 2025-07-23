LoadPackage("AutomGrp");
RootAut := function(n)

  return  Concatenation(List([1..n], x-> []), [PermListList([1..n],Concatenation([2..n],[1]))]) ;

end;

DirectedAutB := function(vector,j)

    local i , l ;

    l := [] ; 

    for i in [1..Length(vector)]
        do 
            if vector[i] = 0 then 

                l[i] := [] ;

            else

                l[i] := List([1..vector[i]],x->1) ;
                l[Length(vector)+1] := [j] ;
            fi;
        od;

    return Concatenation(l,[()]);

end;

# This function generates a GGS group with defining vector <vector> given as a list. 

GGSGenerator := function(vector)

    return SelfSimilarGroup([RootAut(Length(vector)+1), DirectedAutB(vector,2)],["a","b"]) ;
end;

RandomGGS := function(degree)
    local vector;
    vector := List([1..degree - 1], i -> Random([0..degree - 1]));
    while Sum(vector) = 0 do  #while all entries are zero
        vector := List([1..degree - 1], i -> Random([0..degree - 1]));
    od;
    return GGSGenerator(vector);
end;

for degree in [5, 11, 19] do 
    for i in [1..3] do 
        G := RandomGGS(degree);
        Print(G, "\n\t", IsContracting(G), "\n\t", IsFinite(G), "\n\t", IsFiniteState(G), "\n\n");
    od;
od;
