G := AutomatonGroup("a = (b, 1, 1)(1,3,2), b = (1, c, 1)(1,3), c = (b, d, 1)(2,3), d = (1, 1, 1)(2,3)");
# p1 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ] ], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];
# p2 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ]], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];

# p1 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [c], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];
# p2 :=[ (2,3), [ b^2 ], [ 1 ], [ (), [(), [ b ], [ d ], [ 1 ]], [(1,3), [(),[b],[b],[d]]], [ 1 ] ] ];

p1 := [b];
p2 := [(1,3), [1], [c], [1]];

comparing_portraits := function(short_port, long_port, level, G, answer, sections)
    # short_port: AutomPortrait(r), long_port: the r we build, level: must start with 1
    # G: our gr, answer: must start as true, sections: must start as []

    local equality_check, i, current_section;

    if answer = false then
        return false;
    fi;

    Print("Level ", level, ": ", long_port, "\n");

    section_nums := sections;

    tf := answer;

    if Length(short_port) = 1 and Length(long_port) = 1 then # both in (quasi)nucleus
        equality_check := (short_port[1] = long_port[1]);
        Print("comparing ", short_port, " and ", long_port, "\n");

        if equality_check = false then      # CAN'T COMPARE 1S
            if short_port[1] = One(G) and long_port[1] = 1 then
                equality_check := true;
            else
                Print("false", "1\n");
                tf := false;
            fi;
        fi;

        return tf;
    fi;

    if Length(short_port) = 1 then
        # comparing sections
        for i in [2..Length(long_port)] do
            Print("Comparing sections....\n");
            Print("Section nums: ", section_nums, "\n");
            # equality_check := (Section() = long_port[1]);
            
            if Length(long_port[i]) > 1 then
                # take first (level - 1) elements of the list
                section_nums := List([1..(level-1)], i -> section_nums[i]);

                Append(section_nums, [i-1]);
                Print("\n", section_nums, "\n");

                # now compare sections
                Print("Section nums: ", section_nums, "\n");
                for i in [1..Length(section_nums)] do 
                    if i = 1 then
                        current_section := Section(short_port[1], i);
                        Print("current section: ", current_section, "\n");
                    else
                        current_section := Section(current_section, i);
                        Print("current section: ", current_section, "\n");
                    fi;
                od;

                # comparing permutations
                Print("comparing permutations ", AutomPortrait(current_section)[1], " and ", long_port[1], "\n");
                equality_check := (AutomPortrait(current_section)[1] = long_port[1]);

                if equality_check = false then
                    Print("false", "2\n");
                    tf := false;
                    return false;
                fi;

                Print("recursive call (len(s_p)=1)\n");
                comparing_portraits(AutomPortrait(current_section), long_port[i], level + 1, G, tf, section_nums);

            else
                # comparing permutations
                Print("comparing permutations ", PermOnLevel(short_port[1], 1), " and ", long_port[1], "\n");
                equality_check := (PermOnLevel(short_port[1], 1) = long_port[1]);

                if equality_check = false then
                    Print("false", "2\n");
                    tf := false;
                    return false;
                fi;
                comparing_portraits(AutomPortrait(Section(short_port[1], i-1)), long_port[i], level + 1, G, tf, section_nums); 
            fi;

            
            if equality_check = false then
                tf := false;
                Print("false3", "\n");
                return false;
            fi;
        od;

    else
        # comparing permutations
        equality_check := (short_port[1] = long_port[1]);
        Print("\t", short_port[1], "\n");
        Print("\t", long_port[1], "\n");

        if equality_check = false then
                tf := false;
                Print("false4", "\n");
                return false;
        fi;

        # comparing sections
        for i in [2..Length(long_port)] do
            if Length(long_port[i]) > 1 then
                # take first (level - 1) elements of the list
                Print("Section_nums2: ", section_nums, "\n");
                section_nums := List([1..(level-1)], i -> section_nums[i]);

                Append(section_nums, [i-1]);
                Print("\n", section_nums, "\n");
                Print("recursive call, len(s_p) > 1\n");
                Print("s_p i: ", short_port[i], "\n");
                Print("l_p i: ", long_port[i], "\n");
                comparing_portraits(short_port[i], long_port[i], level + 1, G, tf, section_nums);

            else
                # take first (level - 1) elements of the list
                Print("Section_nums2: ", section_nums, "\n");
                section_nums := List([1..(level-1)], i -> section_nums[i]);

                Append(section_nums, [i-1]);
                Print("\n", section_nums, "\n");
                Print("recursive call, len(s_p) > 1\n");
                Print("s_p i: ", short_port[i], "\n");
                Print("l_p i: ", long_port[i], "\n");
                comparing_portraits(short_port[i], long_port[i], level + 1, G, tf, section_nums);
            fi;
        od;
    fi;

    return tf;
end;

test := comparing_portraits(p1,p2,1,G,true, []);