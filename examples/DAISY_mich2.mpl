read "../GlobalIdentifiability.mpl";

sigma := table([
  mu = [km, p12, p21, vmax],
  x_vars = [x1_, x2_],
  y_vars = [y1_, y2_],
  u_vars = [u],
  x_eqs = [
    x1_1 = p12 *x2_0 - p21 * x1_0 + u0 - vmax * x1_0 /(km + x1_0),
    x2_1 = -p12 * x2_0 + p21 * x1_0
  ],
  y_eqs = [
    y1_0 = x1_0,
    y2_0 = x2_0
  ]
]);

theta_g := GlobalIdentifiability(sigma, [op(sigma[mu]), x1_0, x2_0], 0.99, 2);
print(theta_g);
