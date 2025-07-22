for i in [1..10] do 
    Reset(GlobalMersenneTwister,CurrentDateTimeString());

    # want to look at groups of the form <a=(1,w1)(1 2), b=(w2,w2^c)>
    # all abelian i am thinking

    # build random strings of as and bs for w1 and w2
    gens := ["a", "b", "a^-1", "b^-1"];
    w1 := "";
    w2 := "";
    c := "";
    w2_CONJUGATED := "";

    w1_len := Random([1..3]);
    w2_len := Random([1..3]);
    c_len := Random([1..3]);

    for i in [1..w1_len] do 
        current := Random(gens);
        Append(w1, current);
        
        if i <> w1_len then
            Append(w1,"*");
        fi;
    od;

    for i in [1..w2_len] do 
        current := Random(gens);
        Append(w2, current);
        
        if i <> w2_len then
            Append(w2,"*");
        fi;
    od;

    w2_CONJUGATED := Concatenation(w2,"*");

    for i in [1..c_len] do 
        current_idx := Random([1..4]);
        current := gens[current_idx];
        current_inverse := gens[((current_idx + 1) mod 4)+1];
        Append(c, current);

        Append(w2_CONJUGATED, gens[current_idx]);
        w2_CONJUGATED := Concatenation(current_inverse, "*", w2_CONJUGATED);
        
        if i <> c_len then
            Append(c,"*");
            Append(w2_CONJUGATED,"*");
        fi;
    od;

    #plug into SelfSimilarGroup

    SS_str := Concatenation("a=(1,", w1, ")(1,2),b=(", w2, ",", w2_CONJUGATED, ")");

    SSG := SelfSimilarGroup(SS_str);
    Print("SSG := ", SSG);
    Print("\n\n");


    timer_call := IO_CallWithTimeoutList(rec(seconds := 1), IsFinite, [SSG]);

    if timer_call[1] then
        Print(timer_call[2], "\n");
    else 
        Print("isFinite inconclusive\n");
    fi;

    timer_call := IO_CallWithTimeoutList(rec(seconds := 1), Order, [a]);

    if timer_call[1] then
        Print(timer_call[2], "\n");
    else 
        Print("order of a inconclusive\n");
    fi;


    timer_call := IO_CallWithTimeoutList(rec(seconds := 1), Order, [b]);

    if timer_call[1] then
        Print(timer_call[2], "\n");
    else 
        Print("order of b inconclusive\n");
    fi;



    Print("CHECKING QUOTIENT GROUPS ON LEVELS 5 & 7\n");
    tf := PermGroupOnLevel(SSG,5) = Center(PermGroupOnLevel(SSG,5));

    if tf then 
        Print("\t", tf, "\n");

    else
        Print("************************FALSE**************************\n");
    fi;

    tf := PermGroupOnLevel(SSG,7) = Center(PermGroupOnLevel(SSG,7));
    if tf then 
        Print("\t", tf, "\n");

    else
        Print("************************FALSE**************************\n");
    fi;
    

    Print("CHECKING IF FINITE STATE\n");
    timer_call := IO_CallWithTimeoutList(rec(seconds := 5), IsFiniteState, [SSG]);
    if timer_call[1] then
        Print(timer_call[2], "\n");
    else 
        Print("\tisFiniteState inconclusive\n");
    fi;

    Print("\n");
od;