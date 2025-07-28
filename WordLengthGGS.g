LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister, CurrentDateTimeString());

GGS_stabilizing_element := function(timer, v, inner_word_lens, conj_lens)
    local new_GGS_gr, RandomSubgroupElementGGS, RandomWordInGenerators, G, d, power, j, CONJUGATOR_LIFTING_DICTIONARY, 
    NextLevelConjugator, ProductOfPieces, RandomStabilizerGGSMostlyId, RandomStabilizerGGSMostlyId_WORDLEN, GroupActionOnLevel, 
    ElemMappingAToBOnLevel, RandomStabilizerGGS, f_name, f, word_info, lift_power, b_lift, v_str, c, i, timer_call, totalTime;

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
    # v := [Random([1..3]),Random([0..3]),Random([0..3]),0];
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

    RandomStabilizerGGSMostlyId_WORDLEN := function(max_time_SECONDS, innerWordLength, conjugatorLength)
        local current_level, current_element, current_word, all_wordlens, LiftOneLevel, total_time, time_left, start_time;
        
        start_time := NanosecondsSinceEpoch()/(10.0^9);

        current_level := 0;
        total_time := NanosecondsSinceEpoch()/(10.0^9);

        LiftOneLevel := function(word)
            local time_elapsed, lifted_element, piece, newConjugator, commutator, wordLen;
            time_elapsed := NanosecondsSinceEpoch()/(10.0^9);

            lifted_element := [];
            for piece in word do 
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
            
            word := lifted_element;

            # word length stuff here!
            current_word := Word(ProductOfPieces(word));
            wordLen := Length(current_word);

            return [word, Length(current_word), (NanosecondsSinceEpoch()/(10.0^9.0) - time_elapsed)];
        end;

        all_wordlens := [];

        # Represent an element of N by list of [generator, conjugator] factors
        # Where each conjugator is a list of numbers representing generators
        current_element := List([1..innerWordLength], i -> [Random([1..2]), RandomWordInGenerators(conjugatorLength, 2)]); # was cL,3
        
        # initial word
        current_word := Word(ProductOfPieces(current_element));
        Append(all_wordlens, [Length(current_word)]);

        total_time := NanosecondsSinceEpoch()/(10.0^9) - total_time;
        time_left := max_time_SECONDS - total_time;

        timer_call := IO_CallWithTimeoutList(rec(seconds := max_time_SECONDS), LiftOneLevel, [current_element]);
        while timer_call[1] do 
            current_level := current_level + 1;
            Append(all_wordlens, [timer_call[2][2]]);

            # Print("\tword: ", current_word, "\n");

            time_left := max_time_SECONDS + start_time - NanosecondsSinceEpoch()/(10.0^9);

            if time_left <= 0.0 then
                break;
            fi;

            total_time := total_time + timer_call[2][3];


            timer_call := IO_CallWithTimeoutList(rec(seconds := time_left), LiftOneLevel, [timer_call[2][1]]);
        od;
        return [[innerWordLength, conjugatorLength], all_wordlens];
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

    f_name := "lifting_word_length.csv";
    f := OutputTextFile(f_name, true);
    # save a list of each level and corresponding word length
    # then append the list to a file, with col 3 being level 0
    # col 1: commutator length
    # col 2: conjugator length
    # test for different lengths of commutator/conjugator


    for i in inner_word_lens do
        for c in conj_lens do
            v_str := "";
            Append(v_str,"[");
            for j in v do
                Append(v_str,String(j));
                Append(v_str, " ");
            od;
            Append(v_str, "]");

            AppendTo(f_name, v_str);
            AppendTo(f_name, ",");

            AppendTo(f_name, Length(v)+1);
            AppendTo(f_name, ",");

            totalTime := NanosecondsSinceEpoch()/(10.0^9);
            word_info := RandomStabilizerGGSMostlyId_WORDLEN(timer, i, c);
            totalTime := NanosecondsSinceEpoch()/(10.0^9) - totalTime;


            AppendTo(f_name, word_info[1][1]);
            AppendTo(f_name, ",");
            AppendTo(f_name, word_info[1][2]);
            AppendTo(f_name, ",");

            for j in Reversed(word_info[2]) do
                AppendTo(f_name, j);
                AppendTo(f_name, ",");
            od;
            AppendTo(f_name, "\n");
        od;

        # fake flush
        CloseStream(f);
        f := OutputTextFile(f_name, true);
    od;


    # word_info := RandomStabilizerGGSMostlyId_WORDLEN(l, inner_word_len, conj_len); # now lists
    CloseStream(f);
    return word_info;
end;

# Random([2..2]),
# ,Random([3..3])

# random vector from 0 to p-1 for each
# Print(GGS_stabilizing_element(30.0, [Random([1..3]),Random([1..3]),Random([1..3]),0],[1,2],[1,2])); # should be [1,3,5]



# SETTING UP FOR TESTING

# we want: 
    # degree 3/11/19
    # randomly define 5 vectors
    # 10 trials/vectors
    # 10 min / trial
    # inner word length: [1,3,5]
    # outer word length: [1,3,5]


DEGREE := 3; # will be 3/11/19

DEFINING_VECTOR := List([1..(DEGREE-1)], i -> Random([0..(DEGREE-1)]));
DEFINING_VECTOR[1] := Random([1..(DEGREE-1)]);
DEFINING_VECTOR[Length(DEFINING_VECTOR)] := 0;

NUM_TRIALS := 10;
TIME_LIMIT := 600.0;

# random vector from 0 to p-1 for each

for i in [1..NUM_TRIALS] do 
    Print(GGS_stabilizing_element(TIME_LIMIT, DEFINING_VECTOR, [1,3,5],[1,3,5])); #FIXME: should be TIME_LIMIT
od;
