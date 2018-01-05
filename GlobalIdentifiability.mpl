with(LinearAlgebra):
with(VectorCalculus):
with(Grid):

  MakeDerivative := proc(var_name, der_order):
    cat(var_name, der_order):
  end proc:

  ##########################################

  DifferentiateOnce := proc(diff_poly, var_list, max_ord) local result, i, j:
    result := 0:
    for i from 1 to nops(var_list) do
      for j from 0 to max_ord do
        result := result + diff(diff_poly, MakeDerivative(var_list[i], j)) * MakeDerivative(var_list[i], j + 1):
      end do:
    end do:
    simplify(result):
  end proc:

  ##########################################

  Differentiate := proc(diff_poly, var_list, max_ords, ord := 1) local result, i;
    result := diff_poly:
    for i from 1 to ord do
      result := DifferentiateOnce(result, var_list, max_ords):
    end do:
    result:
  end proc:

  ##########################################

  GetVars := proc(diff_poly, var_list, max_ord) local all_vars, result;
    all_vars := map( v -> op(map( i -> MakeDerivative(v, i), [`$`(0..max_ord)] )), var_list):
    result := select(v -> evalb(diff(diff_poly, v) <> 0), all_vars):
    result:
  end proc:

  ###########################################

  GetOrderVar := proc(diff_var, var_list, max_ord)
  local result, v, h;
    result := -1:
    for v in var_list do
      for h from 0 to max_ord do
        if diff(diff_var, MakeDerivative(v, h)) <> 0 then
          result := [h, v];
        end if;
      end do:
    end do:
    result;
  end proc:

  ##########################################

  SamplePoint := proc(bound, sigma)
    local n, m, s, all_params, all_vars, theta_hat, u_variables, u_hat, x_hat, y_hat, eq, eq_num, eq_denom, 
    v, poly, i, j, all_subs, roll;
    n := nops(sigma[x_vars]):
    m := nops(sigma[y_vars]):
    s := nops(sigma[mu]) + n:
    all_params := [op(sigma[mu]), op(map(x -> MakeDerivative(x, 0), sigma[x_vars] ))]:
    all_vars := [ op(sigma[x_vars]), op(sigma[y_vars]), op(sigma[u_vars]) ]:

    roll := rand(0 .. bound):
    theta_hat := map(p -> p = roll(), all_params): 
    u_variables := [];
    for i from 1 to nops(sigma[u_vars]) do
      u_variables := [ op(u_variables), seq(MakeDerivative(sigma[u_vars][i], j), j = 0..s) ]:
    end do:
    u_hat := map(p -> p = roll(), u_variables) :   

    x_hat := [];
    for i from 1 to n do:
      eq := sigma[x_eqs][i]:
      eq_num := numer(lhs(eq) - rhs(eq));
      eq_denom := denom(lhs(eq) - rhs(eq));
      for j from 0 to s do
        v := Differentiate(lhs(eq), all_vars, s, j);
        poly := v * eq_denom - Differentiate( eq_num, all_vars, s, j );
        x_hat := [op(x_hat), v = poly / eq_denom];
      end do:
    end do:
    y_hat := [];
    for i from 1 to m do:
      eq := sigma[y_eqs][i]:
      eq_num := numer(lhs(eq) - rhs(eq));
      eq_denom := denom(lhs(eq) - rhs(eq));
      for j from 0 to s do
        v := Differentiate(lhs(eq), all_vars, s, j);
        poly := v * eq_denom - Differentiate( eq_num, all_vars, s, j );
        y_hat := [op(y_hat), v = poly / eq_denom];
      end do:
    end do:
    all_subs := [op(theta_hat), op(u_hat)]:
    for i from 1 to s + 1 do
      x_hat := map(e -> lhs(e) = subs(all_subs, rhs(e)), x_hat):
      y_hat := map(e -> lhs(e) = subs(all_subs, rhs(e)), y_hat):
      all_subs := [ op(all_subs), op(select(e -> type(rhs(e), numeric), [op(x_hat), op(y_hat)])) ]:
    end do:

    [y_hat, u_hat, theta_hat, all_subs];
  end proc:


  ##########################################

  GlobalIdentifiability := proc(sigma, theta_l, p := 0.99, method := 1) 
    local i, j, n, m, s, all_params, all_vars, eqs, Q, X, Y, poly, d0, D1, sample, all_subs,
    alpha, beta, Et, x_theta_vars, was_added, eqs_i, JacX, vars, vars_to_add, ord_var, var_index, 
    deg_variety, D2, y_hat, u_hat, theta_hat, Et_hat, Q_hat, theta_g, gb, v:
    n := nops(sigma[x_vars]):
    m := nops(sigma[y_vars]):
    s := nops(sigma[mu]) + n:
    all_params := [op(sigma[mu]), op(map(x -> MakeDerivative(x, 0), sigma[x_vars] ))]:
    all_vars := [ op(sigma[x_vars]), op(sigma[y_vars]), op(sigma[u_vars]) ]:

    eqs := [op(sigma[x_eqs]), op(sigma[y_eqs])]:
    Q := foldl( (f, g) -> lcm(f, g), op( map(f -> denom(rhs(f)), eqs) )):
    X := []:
    for i from 1 to n do
      poly := simplify( Q * (lhs(sigma[x_eqs][i]) - rhs(sigma[x_eqs][i])) ):
      X := [op(X), map( j -> Differentiate(poly, all_vars, s, j), [seq(j, j = 0..s)] )]:
    end do:
    Y := []:
    for i from 1 to m do
      poly := simplify( Q * (lhs(sigma[y_eqs][i]) - rhs(sigma[y_eqs][i])) ):
      Y := [op(Y), map( j -> Differentiate(poly, all_vars, s, j), [seq(j, j = 0..s)] )]:
    end do:

    d0 := max(op( map(f -> degree( simplify(Q * rhs(f)) ), eqs) ), degree(Q)):
 
    D1 := floor( 2 * d0 * s * (n + 1) * (1 + 2 * d0 * s) / (1 - p) ):
    print("Bound D_1  ", D1);
    sample := SamplePoint(D1, sigma):
    all_subs := sample[4]:
    while subs(all_subs, Q) = 0 do
      sample := SamplePoint(D1, sigma):
      all_subs := sample[4]:
    end do:
    
    alpha := [seq(1, i = 1..n)]:
    beta := [seq(0, i = 1..m)]:
    Et := [];
    x_theta_vars := all_params:
    was_added := 1:
    while was_added = 1 do
      was_added := 0:
      for i from 1 to m do
        eqs_i := [op(Et), Y[i][beta[i] + 1]]:
        JacX := subs(all_subs, Jacobian(eqs_i, x_theta_vars = subs(all_subs, x_theta_vars)));
        if Rank(JacX) = nops(eqs_i) then
          was_added := 1:
          Et := [op(Et), Y[i][beta[i] + 1]]:
          beta[i] := beta[i] + 1:
          for j from 1 to s + 1 do
            vars := {};
            for poly in [op(Et), op( map(i -> Y[i][beta[i] + 1], 1..m) )] do
              vars := vars union { op(GetVars(poly, sigma[x_vars], s + 1)) }:
            end do:
            vars_to_add := { op(remove(v -> evalb(v in x_theta_vars), vars)) };
            for v in vars_to_add do
              x_theta_vars := [op(x_theta_vars), v];
              ord_var := GetOrderVar(v, all_vars, s + 1);
              var_index := ListTools[Search](ord_var[2], sigma[x_vars]):
              poly := X[ var_index ][ ord_var[1] ]:
              Et := [op(Et), poly]:
              alpha[ var_index ] := max(alpha[ var_index ], ord_var[1] + 1):
            end do:
          end do:
        end if:
      end do: 
    end do:

    Et := [op(Et), op( map(i -> Y[i][beta[i] + 1], 1..m) )]:
    for i from 1 to m do
      beta[i] := beta[i] + 1:
    end do:
 
    print("Beta ", beta);
    print("Alpha ", alpha);
    deg_variety := foldl(`*`, op( map(e -> degree(e), Et) )):
    D2 := floor( 6 * nops(theta_l) * deg_variety * (1 + 2 * d0 * max(op(beta))) / (1 - p) ):
    print("Bound D_2 ", D2):
    sample := SamplePoint(D2, sigma):
    while subs(sample[4], Q) = 0 do
      sample := SamplePoint(D2, sigma):
    end do:    
    y_hat := sample[1]:
    u_hat := sample[2]:
    theta_hat := sample[3]:

    Et_hat := map(e -> subs([op(y_hat), op(u_hat)], e), Et):
    vars := { op(sigma[mu]) };
    for poly in Et_hat do
      vars := vars union { op(GetVars(poly, sigma[x_vars], s + 1)) }:
    end do:
    Q_hat := subs(u_hat, Q):

    theta_g := []:
    if method = 1 then
      for i from 1 to nops(theta_l) do
        Grid[Run](i, Groebner[Basis], [ [op(Et_hat), z * Q_hat - 1, (theta_l[i] - subs(theta_hat, theta_l[i])) * w - 1], tdeg(op(vars), z, w) ]):
      end do:
      Grid[Wait]():

      for i from 1 to nops(theta_l) do
        gb := Grid[GetLastResult](i):
        if gb = [1] then
          theta_g := [op(theta_g), theta_l[i]]:
        end if:
      end do:     
    elif method = 2 then
      gb := Groebner[Basis]([op(Et_hat), z * Q_hat - 1], tdeg(op(vars), z));
      for i from 1 to nops(theta_l) do
        if Groebner[NormalForm](theta_l[i], gb, tdeg(op(vars), z)) = subs(theta_hat, theta_l[i]) then
          theta_g := [ op(theta_g), theta_l[i] ]:
        end if:
      end do:
    else
      print("No such method"):
    end if:
    theta_g;
  end proc:

