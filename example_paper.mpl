read "GlobalIdentifiability.mpl";

sigma := table([
  mu = [mu1, mu2],
  x_vars = [x],
  y_vars = [y],
  u_vars = [],
  x_eqs = [
    x1 = 1 / x0
  ],
  y_eqs = [
    y0 = mu2 * x0 + mu1
  ]
]);

theta_g := GlobalIdentifiability(sigma, [mu1, mu2, x0], 0.9, 2);
print(theta_g);
