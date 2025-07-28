new_GGS_gr := function(v)
    # v: defining vector. v[0] <> 1 and v[Length(v)] = 1.
    # Length(v) = degree - 1

    local degree, gen_details, current_gen, i, placeholder, possible_gens, currentGGS, gen_names, L;


    # degree of tree
    degree := Length(v) + 1;

    gen_details := [];

    # adding 1
    current_gen := List([1..degree], i -> 1);
    Append(current_gen, [()]);
    Append(gen_details, [current_gen]);
    
    # adding a
    current_gen := List([1..degree], i -> 1);
    Append(current_gen, [CycleFromList([1..degree])]);
    Append(gen_details, [current_gen]);

    # now making all of the "bonus" generators (a to a power)
    for i in v do 
        if i <> 0 and i <> 1 then 
            current_gen := List([1..degree], i -> 1);
            Append(current_gen, [CycleFromList([1..degree])^i]);
            Append(gen_details, [current_gen]);
        fi;
    od;

    # making b
    current_gen := [];
    placeholder := 4;

    for i in [1..Length(v)] do 
        if v[i] = 0 then
            Append(current_gen, [1]);
        elif v[i] = 1 then 
            Append(current_gen, [2]);
        else
            Append(current_gen, [placeholder]);
            placeholder := placeholder + 1;
        fi;
    od;

    Append(current_gen, [3]);   # adding b at the end
    Append(current_gen, [()]);
    
    gen_details := Concatenation(gen_details{[1,2]}, [current_gen], gen_details{[3..Length(gen_details)]});
    
    possible_gens := ["1", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"];
    gen_names := List([1..Length(gen_details)], i -> possible_gens[i]);

    # new automaton group!
    currentGGS := AutomatonGroup(gen_details, gen_names);
    L := GeneratorsOfGroup(currentGGS);
    Print(currentGGS, "\n");

    return Subgroup(currentGGS, [L[1],L[2]]); # so we don't use all the extra variables
end;

#Returns a random element of the subgroup over which a GGS group with defining vector v is branching
RandomSubgroupElementGGS := function(G)
    local g, num_repetitions,a,b;
    g := Random(G);
    num_repetitions := Random([-10..10]);
    return g^-1 * (a^-1*b^-1*a*b)^(num_repetitions) * g;
end;

RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
end;

#Self-replicating equations:
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed

# SETUP HERE!
v := [Random([1..3]),Random([0..3]),Random([0..3]),0];
G := new_GGS_gr(v);

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
                Append(lifted_element, [[1, Concatenation([2], newConjugator)]]);
                Append(lifted_element, [[2, newConjugator]]);
            else 
                Append(lifted_element, [[1, newConjugator]]);
                Append(lifted_element, [[2, Concatenation([2], newConjugator)]]);
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

Print(RandomStabilizerGGS(1,5,1,1));
