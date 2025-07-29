LoadPackage("AutomGrp", false);

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

RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
end;

#Self-replicating equations:
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

# SETUP HERE!
v := [6, 4, 3, 3, 6, 0];
G := GGSGenerator(v);

d := Length(v) + 1;
power := v[1];
for j in [1..d] do
    power := power * j;
    
    if power mod d = 1 then 
        lift_power := j;
        break;
    fi;

    power := v[1];
od;

# setting up lifting dictionary

CONJUGATOR_LIFTING_DICTIONARY := NewDictionary(1, true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 1, List([1..lift_power], i -> 2));
b_lift := List([1..(d-1)], i -> 1);
Append(b_lift, [2,1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, 2, b_lift);

NextLevelConjugator := function(wordOfElement)
    local newGeneratorIndices, i;
    newGeneratorIndices := [];

    for i in wordOfElement do 
        Append(newGeneratorIndices, LookupDictionary(CONJUGATOR_LIFTING_DICTIONARY, i));
    od;
    return newGeneratorIndices;
end;

ProductOfPieces := function(pieces)
    local product, piece, conjugatorWord, conjugator, generator, commutator;
    product := One(G);
    for piece in pieces do 
        #piece = [generator, conjugator]
        conjugatorWord := piece[2];
        conjugator := One(G);
        for generator in conjugatorWord do
            if generator = 1 then 
                conjugator := conjugator * a;
            else
                conjugator := conjugator * b;
            fi;
        od;

        product := product*conjugator^-1;
        commutator := piece[1];
        if commutator = 1 then 
            product := product * (a^-1*b^-1*a*b);
        else
            product := product * (b^-1*a^-1*b*a);
        fi;

        product := product * conjugator;
    od;
    return product;
end;

#Computes random stabilizers of the nth level for the GGS group with vector v. 
#All sections at nth level are identity except first one.

#Lifting equations: 
# [b,b^a] = [a,b]^b * [b,a] = ([a,b],1,...,1)
# [b,b^a]^-1 = [a,b] * [b,a]^b = ([b,a],1,...,1)
RandomStabilizerGGSMostlyId := function(level, innerWordLength, conjugatorLength)
    local current_level, current_element, lifted_element, piece, newConjugator,
        commutator;
    current_level := 0;
    #Represent an element of N by list of [generator, conjugator] factors
    #Where each conjugator is a list of numbers representing generators
    current_element := List([1..innerWordLength], i -> [Random([1..2]), RandomWordInGenerators(conjugatorLength, 2)]); # was cL,3
    while current_level < level do 
        lifted_element := [];
        for piece in current_element do 
            #piece = [generator, conjugator]
            newConjugator := NextLevelConjugator(piece[2]);
            commutator := piece[1];

            if commutator = 1 then 
                Append(lifted_element, [[1, Concatenation(List([1..lift_power], i -> 2), newConjugator)]]);
                Append(lifted_element, [[2, newConjugator]]);
            else 
                Append(lifted_element, [[1, newConjugator]]);
                Append(lifted_element, [[2, Concatenation(List([1..lift_power], i -> 2), newConjugator)]]);
            fi;
        od;
        
        current_element := lifted_element;
        current_level := current_level + 1;
    od;
    return ProductOfPieces(current_element);
end;

GroupActionOnLevel := function(level)
    return function(point, g)
        return point^PermOnLevel(g, level);
    end;
end;

ElemMappingAToBOnLevel := function(G, a, b, level)
    local action;
    action := GroupActionOnLevel(level);
    return RepresentativeAction(G, a, b, action);
end;

RandomStabilizerGGS := function(level, degree, innerWordLength, conjugatorLength)
    local liftedSections, product, conjugator, i;
    liftedSections := List([1..degree^level], i -> RandomStabilizerGGSMostlyId(level, innerWordLength, conjugatorLength));
    product := liftedSections[1];
    for i in [2..degree^level] do
        conjugator := ElemMappingAToBOnLevel(G, 1, i, level);
        product := product * liftedSections[i]^conjugator;
    od;
    return product;
end;

