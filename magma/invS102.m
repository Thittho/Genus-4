f := f; // 1

I2 := Transvectant(f, f, 10); // 2
c24 := Transvectant(f, f, 8); // 3
c28 := Transvectant(f, f, 6); // 4
c212 := Transvectant(f, f, 4); // 5
c216 := Transvectant(f, f, 2); // 6

c32 := Transvectant(c28, f, 8); // 7
c36_1 := Transvectant(c24, f, 4); // 8
c36_2 := Transvectant(c212, f, 8); // 9
c312_1 := Transvectant(c216, f, 7); // 12
c312_2 := Transvectant(c212, f, 5); // 13
c314 := Transvectant(c216, f, 6); // 14
c316 := Transvectant(c216, f, 5); // 15
c318 := Transvectant(c216, f, 4); // 16
c320 := Transvectant(c216, f, 3); // 17
c324 := Transvectant(c216, f, 1); // 18

I4 := Transvectant(c24, c24, 4); // 19
c44_2 := Transvectant(c312_2, f, 9); // 21
c44_3 := Transvectant(c312_1, f, 9); // 22
c46 := Transvectant(c316, f, 10); // 23
c48_3 := Transvectant(c314, f, 8); // 26
c410_3 := Transvectant(c316, f, 8); // 29
c412_1 := Transvectant(c320, f, 9); // 30
c412_2 := Transvectant(c318, f, 8); // 31
c414_2 := Transvectant(c320, f, 8); // 33
c414_3 := Transvectant(c318, f, 7); // 34


necessary := [i : i in [1..#FdCov] | FdCov[i]`order eq 0 and FdCov[i]`degree mod 2 eq 0];
nec_temp := necessary;
nec_temp2 := []; 

for i in nec_temp do
    if i ne 1 then
        U := Setseq(MultisetToSet(FdCov[i]`U));
        V := Setseq(MultisetToSet(FdCov[i]`V));
        i, U, V;
        for u in U do
            if not u in necessary cat nec_temp cat nec_temp2 then
                Append(~nec_temp2, u);
            end if;
        end for;
        for v in V do
            if not v in necessary cat nec_temp cat nec_temp2 then
                Append(~nec_temp2, v);
            end if;
        end for;
    end if;
end for;
nec_temp2;

necessary cat:= nec_temp2;
nec_temp := nec_temp2;
nec_temp2 := [];

for i in Sort(necessary)[2..#necessary] do
    Write("~/invS10.m", "c" cat Sprint(FdCov[i]`degree) cat Sprint(FdCov[i]`order) cat " := Transvectant(" cat &cat[Sprint(u) cat "*" : u in FdCov[i]`U] cat ", " cat &cat[Sprint(u) cat "*" : u in FdCov[i]`V] cat ", " cat Sprint(FdCov[i]`level) cat "); // " cat Sprint(i));
end for;