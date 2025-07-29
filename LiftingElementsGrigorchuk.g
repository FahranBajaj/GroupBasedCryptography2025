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
        conjugatorWord := piece[2];
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
        commutator := piece[1];
        if commutator = 1 then
            product := product * (a*b)^2;
        else
            product := product * (b*a)^2;
        fi;
        product := product * conjugator;
    od;
    return product;
end;

RandomStabilizerGrigorchukMostlyId := function(level, innerWordLength, conjugatorLength)
    local current_level, current_element, lifted_element, piece, newConjugator,
        commutator;

    current_level := 0;
    current_element := List([1..innerWordLength], i -> [Random([1..2]), RandomWordInGenerators(conjugatorLength, 4)]);
    Print(current_element, "\n");
    while current_level < level do 
        lifted_element := [];
        for piece in current_element do 
            #piece = [generator, conjugator]
            newConjugator := NextLevelConjugator(piece[2], 1);
            commutator := piece[1];
            if commutator = 1 then 
                Append(lifted_element, [[1, Concatenation([1], newConjugator)]]);
                Append(lifted_element, [[1, Concatenation([4,2,1], newConjugator)]]);
            else    
                Append(lifted_element, [[2, Concatenation([4,2,1], newConjugator)]]);
                Append(lifted_element, [[2, Concatenation([1], newConjugator)]]);
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

RandomStabilizerGrigorchuk := function(level, innerWordLength, conjugatorLength)
    local liftedSections, product, conjugator, i;
    liftedSections := List([1..2^level], i -> RandomStabilizerGrigorchukMostlyId(level, innerWordLength, conjugatorLength));
    product := liftedSections[1];
    for i in [2..2^level] do
        conjugator := ElemMappingAToBOnLevel(G, 1, i, level);
        product := product * liftedSections[i]^conjugator;
    od;
    return product;
end;
