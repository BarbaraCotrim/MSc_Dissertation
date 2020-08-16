### PARAMETERS & SETS ###
param n > 1 integer;            # Number prosumers
param t_max > 1 integer;        # Number of time periods
set T:= 1..(t_max);             # Time periods
set I:= 1..n;                   # Prosumers/participants
set C:= 1..7;                   # Inequelity constraints

param B{T} >= 0;                     # Savings per MWh from not purchasing storage
param price_W{T};               # Price on the Wholesale Market
param price_R{T};               # Price on the Retail Market
param S_ini{I} >= 0;            # Initial stored electricity
param S_max{I} >= 0;            # Maximum storage capacity
param G{I,T} >= 0;              # Electricity generated
param D{I,T} >= 0;              # Electricity consumption
param niu  >= 0;                # Round-trip battery efficiency
param B_bar:= (1/t_max*sum{t in T}B[t]); # Average Savings
param comp_A >= 0;              # Compensation for availability
param comp_U >= 0;              # Compensation for use
param commission >= 0;          # Commission

### INITIAL SOLUTION ###
param charged_sol{I,T} >= 0;
param discharged_sol{I,T} >= 0;
param e_A_sol{I,T} >= 0;
param x_sol{I,T} >= 0;
param y_sol{I,T} >= 0;
param e_P_sol{I,T} >= 0;
param lambda_sol{C,I,T} <= 0;
param mu_sol{I,T};
param time_phase_0;

### LEADER VARIABLES ###
var charged{I,T} >= 0;          # Electricity charged
var discharged{I,T} >= 0;       # Electricity discharged
var e_A{I,T} >= 0;              # Electricity that belongs to the aggregator

### FOLLOWERS VARIABLES ###
var x{I,T} >= 0;                # Electricity sold on Day-Ahead market
var y{I,T} >= 0;                # Electricity bought on Retail market
var e_P{I,T} >= 0;              # Electricity that belongs to the aggregator

### AUXILIARY VARIABLES ###
var lambda{C,I,T} <= 0;         # Dual variables of inequality lower-level constraints
var mu{I,T};                    # Dual variables of equality lower-level constraints
var u{I,T} binary;              # Binary variables of MIF of constraint (2)
var z{C,I,T} binary;            # Binary variables of MIF of KKT complementarities

### AUX VAR FOR REGULARIZATION ###
param r;       # Slackness of the complementarity
set ITER;      # Iterations counter
param rho;     # Scalar used to update the value of r

### AUX VAR FOR MIXED INTEGER FORMULATION ###
param M_1{C};
param M_2{C};


# --------------------------------------------------------------------------------------------------------
# REGULARIZATION
# --------------------------------------------------------------------------------------------------------
### OBJECTIVE ###
# No demand curves
#maximize profit_aggregator: sum {i in I,t in T}(B[t]*(S_max[i]-e_P[i,t]) +
#									            price_W[t]*(discharged[i,t]-charged[i,t]) +
#									            (commission)*price_W[t]*x[i,t] -
#									            (comp_A)*(S_max[i]-e_P[i,t]-e_A[i,t]) -
#									            (comp_U)*e_A[i,t]);
# Linear demand curves
maximize profit_aggregator: sum {i in I,t in T}(((comp_A+comp_U)/(2*B_bar))*B[t]*(S_max[i]-e_P[i,t]) +
									            (comp_U/B_bar)*price_W[t]*(discharged[i,t]-charged[i,t]) +
									            (-commission^2+commission)*price_W[t]*x[i,t] -
									            (comp_A^2/B_bar)*(S_max[i]-e_P[i,t]-e_A[i,t]) -
									            (comp_U^2/B_bar)*e_A[i,t]);

### UPPER_LEVEL CONSTRAINTS ###
subject to sell {i in I,t in T}: discharged[i,t] <= (1-u[i,t])*S_max[i];  # Constraint 2 Mixed Integer
subject to buy {i in I,t in T}: charged[i,t] <= u[i,t]*(S_max[i]/niu);    # Constraint 2 Mixed Integer
subject to aggregator_fairness {i in I}: niu*sum{t in T}(charged[i,t]) = sum{t in T}(discharged[i,t]); # Constraint 3
subject to ESS_max_cap {i in I,t in T}: e_A[i,t] <= S_max[i];
subject to update_e_A {i in I,t in T: t>1}: e_A[i,t] = e_A[i,t-1] + niu*charged[i,t-1] - discharged[i,t-1]; # Constraint 5
subject to initiate_e_A {i in I, t in T: t=1}: e_A[i,t] = 0; # Constraint 5

### LOWER_LEVEL KKT CONDITIONS ###
# Primal feasibility
subject to buy_needed {i in I, t in T}: y[i,t] >= D[i,t]-e_P[i,t]-G[i,t];
subject to buy_limit {i in I, t in T}: y[i,t] <= D[i,t];
subject to sell_limit {i in I, t in T}: x[i,t] <= G[i,t];
subject to max_cap {i in I,t in T}: e_A[i,t] + e_P[i,t] <= S_max[i];
subject to update_e_P {i in I,t in T: t>1}: e_P[i,t] = e_P[i,(t-1)] + niu*(G[i,(t-1)]+y[i,(t-1)]-D[i,(t-1)]-x[i,(t-1)]);
subject to initiate_e_P {i in I, t in T: t=1}: e_P[i,t] = S_ini[i];

# Stationarity/Dual feasibility
subject to stat_x {i in I,t in T: t<t_max}: (commission-1)*price_W[t] - lambda[3,i,t] + lambda[5,i,t] - niu*mu[i,t+1] = 0;
subject to stat_x_T {i in I, t in T: t=t_max}: (commission-1)*price_W[t] - lambda[3,i,t] + lambda[5,i,t] = 0;
subject to stat_y {i in I,t in T: t<t_max}: price_R[t] + lambda[1,i,t] - lambda[2,i,t] + lambda[6,i,t] + niu*mu[i,t+1] = 0;
subject to stat_y_T {i in I, t in T: t=t_max}: price_R[t] + lambda[1,i,t] - lambda[2,i,t] + lambda[6,i,t] = 0;
subject to stat_e {i in I,t in T: t<t_max}: comp_A + lambda[1,i,t] - lambda[4,i,t] + lambda[7,i,t] + (mu[i,t+1]-mu[i,t]) = 0;
subject to stat_e_T {i in I, t in T: t=t_max}: comp_A + lambda[1,i,t] - lambda[4,i,t] + lambda[7,i,t] - mu[i,t] = 0;

# Regularised Complementarity
# Constraint 2
subject to reg_cons_2 {i in I,t in T}: charged[i,t] * discharged[i,t] <= r;
# KKT complementarities
subject to reg_comp_1 {i in I,t in T}: lambda[1,i,t] * (-y[i,t]+D[i,t]-e_P[i,t]-G[i,t]) <= r;
subject to reg_comp_2 {i in I,t in T}: lambda[2,i,t] * (y[i,t]-D[i,t]) <= r;
subject to reg_comp_3 {i in I,t in T}: lambda[3,i,t] * (x[i,t]-G[i,t]) <= r;
subject to reg_comp_4 {i in I,t in T}: lambda[4,i,t] * (e_A[i,t]+e_P[i,t]-S_max[i]) <= r;
subject to reg_comp_5 {i in I,t in T}: lambda[5,i,t] * (-x[i,t]) <= r;
subject to reg_comp_6 {i in I,t in T}: lambda[6,i,t] * (-y[i,t]) <= r;
subject to reg_comp_7 {i in I,t in T}: lambda[7,i,t] * (-e_P[i,t]) <= r;
