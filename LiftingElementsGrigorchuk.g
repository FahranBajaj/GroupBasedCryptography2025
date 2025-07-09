LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister, CurrentDateTimeString());

RandomWordInGenerators := function(len, num_generators)
    local choicesOfGenerators;
    choicesOfGenerators := List([1..len], i -> Random([1..num_generators]));
    return choicesOfGenerators;
    
    #wordFunction := function(generators)
    #    factors := [];
    #    for i in [1..len] do
    #        if inverses[i] then 
    #            factor := generators[choicesOfGenerators[i]]^-1;
    #        else 
    #            factor := generators[choicesOfGenerators[i]];
    #        fi;
    #    od;
    #    return Product(factors);
    #end;
    #return wordFunction;
end;

G := AutomatonGroup("a=(1,1)(1,2), b=(a,c), c=(a,d), d=(1,b)"); # grigorchuk group
CONJUGATOR_LIFTING_DICTIONARY := NewDictionary([1, 1], true);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [1, 1], [2]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [2, 1], [1, 4, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [3, 1], [1, 2, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [4, 1], [1, 3, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [1, 2], [1, 2, 1]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [2, 2], [4]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [3, 2], [2]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [4, 2], [3]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [0, 1], [0]);
AddDictionary(CONJUGATOR_LIFTING_DICTIONARY, [0, 2], [0]);


NextLevelConjugator := function(wordOfElement, sectionNumber)
    local newGeneratorIndices, i;
    newGeneratorIndices := [];

    for i in wordOfElement do 
        Append(newGeneratorIndices, LookupDictionary(CONJUGATOR_LIFTING_DICTIONARY, [i, sectionNumber]));
    od;
    return newGeneratorIndices;
end;

ProductOfPieces := function(pieces)
    local product, piece, conjugatorWord, conjugator, generator, commutatorWord,
         commutator;
    product := One(G);
    for piece in pieces do 
        conjugatorWord := piece[1];
        conjugator := One(G);
        for generator in conjugatorWord do
            if generator = 0 then
                conjugator := conjugator * One(G);
            elif generator = 1 then 
                conjugator := conjugator * a;
            elif generator = 2 then 
                conjugator := conjugator * b;
            elif generator = 3 then
                conjugator := conjugator * c;
            else
                conjugator := conjugator * d;
            fi;
        od;

        product := product*conjugator^-1;
        commutatorWord := piece[2];
        for commutator in commutatorWord do 
            if commutator = 0 then
                product := product * One(G);
            else
                product := product * (a*b)^2;
            fi;
        od;
        product := product * conjugator;
        Print("\t~ ", product, "\n");
    od;
    Print("final product: ", product, "\n");
    return product;
end;

#Computes random stabilizers of the nth level for the iterated monodromy
#group for z^2 + i
RandomStabilizerGrigorchuk := function(level, innerWordLength, conjugatorLength)
    local current_level, stabilizers_of_level, i, conjugator, innerWord, stabilizers_of_next_level,
        pointer, pieces_of_next_stabilizer, section1, piece, newConjugator, 
        commutator, section2;
    current_level := 0;
    stabilizers_of_level := [];
    Print("conjugators and inner words on level ", level, ":\n");
    for i in [1..2^level] do 
        if i = 1 then
            conjugator := RandomWordInGenerators(conjugatorLength, 4);
            Print("\tconjugator ", i, ": ", conjugator, "\n");
            innerWord := RandomWordInGenerators(innerWordLength, 2);    # Q: what is this for?
            Print("\tinner word ", i, ": ", innerWord, "\n");
            Append(stabilizers_of_level, [[[conjugator, innerWord]]]);
        else
            Append(stabilizers_of_level, [[[[0],[0]]]]);
        fi;
    od;

    while current_level < level do 
        stabilizers_of_next_level := [];
        pointer := 1;
        while pointer < Length(stabilizers_of_level) do 
            pieces_of_next_stabilizer := [];
            section1 := stabilizers_of_level[pointer];
            for piece in section1 do 
                newConjugator := NextLevelConjugator(piece[1], 1);

                for commutator in piece[2] do
                    if commutator = 0 then
                        Append(pieces_of_next_stabilizer, [[newConjugator, [0]]]);
                    else 
                        Append(pieces_of_next_stabilizer, [[Concatenation([1], newConjugator), [1]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([4,2,1], newConjugator), [1]]]);
                    fi;
                od;
            od;
            pointer := pointer + 1;
            section2 := stabilizers_of_level[pointer];
            for piece in section2 do 
                newConjugator := NextLevelConjugator(piece[1], 2);
                for commutator in piece[2] do 
                    if commutator = 0 then
                        Append(pieces_of_next_stabilizer, [[newConjugator, [0]]]);
                    else 
                        Append(pieces_of_next_stabilizer, [[Concatenation([1], [1], newConjugator), [1]]]);
                        Append(pieces_of_next_stabilizer, [[Concatenation([4,2,1], [1], newConjugator), [1]]]);
                    fi;
                od;
            od;
            Append(stabilizers_of_next_level, [pieces_of_next_stabilizer]);
            pointer := pointer + 1;
        od;
        current_level := current_level + 1;
        stabilizers_of_level := stabilizers_of_next_level;
        stabilizers_of_next_level := [];
    od;
    return ProductOfPieces(stabilizers_of_level[1]);
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

treeAut := RandomStabilizerGrigorchuk(2,1,1);