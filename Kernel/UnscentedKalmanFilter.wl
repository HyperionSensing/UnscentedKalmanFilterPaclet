(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["UnscentedKalmanFilter`"]


(* ::Subsection:: *)
(*Sigma Points*)


UKFSigmaPoints::usage = "
UKFSigmaPoints[{___, \[Mu], P}, \[CapitalDelta], \[Kappa]] generates {sigma points, weights} using constant \[Kappa] for a probability distribution with mean \[Mu] and covariance P, after shifting it by \[CapitalDelta]. \[Mu] must be a list and P a matrix. 
UKFSigmaPoints[{___, \[Mu], P}, \[CapitalDelta]] := generates {sigma points, weights} for a probability distribution with mean \[Mu] and covariance P with \[Kappa] chosen automatically to match some of the forth moments of the input distribution, assuming it is guassian.
UKFSigmaPoints[{___, \[Mu], P}] generates {sigma points, weights} where \[CapitalDelta] is the zero vector.
";

UKFSigmaPointsMean::usage = "
UKFSigmaPointsMean[sigmaPoints] calculates the estimated mean of the distribution approximated by a set of sigma points.";

UKFSigmaPointsCovariance::usage = "
UKFSigmaPointsCovariance[sigmaPoints, \[Mu]] calculates the estimated covariance of the distribution approximated by a set of sigma points relative to the mean \[Mu]. 
UKFSigmaPointsCovariance[{\[Sigma]s_, ws_}] will automatically calculate the mean";

UKFSigmaPointsCrossCovariance::usage = "
UKFSigmaPointsCrossCovariance[sigmaPointsX, sigmaPointsY, \[Mu]X, \[Mu]Y] calculates the estimated cross covariance of the distribution approximated by a two sets of sigma points";
 


(* ::Subsection:: *)
(*System*)


UKFSystemQ::usage = "UKFSystemQ[association] returns true if association is a valid UKF system. 
A valid system must have ProcessModel, MeasurementModel, ProcessNoise, and MeasurementNoise keys.  ProcessModel, i.e. f[state, \[CapitalDelta]t], is the process model function. MeasurementModel, i.e. h[state] is the measurement model function.  processNoise and measurementNoise must be covariance matrices. 
A system may also have a Parameters key; this is a list of rules that will get applied to ProcessModel and MeasurementModel before they are used. ";

UKFFilterResultsQ::usage = "UKFFilterResultsQ[association] returns true if association is a valid result returned by UKFFilter";

UKFSmootherResultsQ::usage = "UKFSmootherResultsQ[association] returns true if association is a valid result returned by UKFFilter";


(* ::Subsection:: *)
(*Update & Prediction*)


UKFPredict::usage = 
"UKFPredict[state, system] performs the prediction step of the Unscented Kalman Filter (UKF). \
The argument 'state' is a list {x, P}, where x is the current state estimate and P is the current state covariance matrix. \
The argument 'system' is a UKFSystem, see UKFSystemQ";

UKFUpdate::usage = 
"UKFUpdate[state, z, system] performs the update step of the Unscented Kalman Filter (UKF). \
The argument 'state' is a list {x, P}, where x is the predicted state estimate and P is the predicted state covariance matrix. \
'z' is the measurement vector of the form {time, {__}}. 
The argument 'system' is a UKFSystem, see UKFSystemQ.";

UKFBackwardsUpdate::usage = 
"UKFBackwardsUpdate[state, subsequentState, system] updates a state conditioned only on previous data given the subsequent state that is conditioned on all data. This is used in the RTS algorithm.";


(* ::Subsection:: *)
(*Filtering & Smoothing*)


UKFFilter::usage = 
"UKFFilter[initialEstimate, measurements, system] performs Unscented Kalman Filtering (UKF) to estimate the state of a dynamic system over time. \
'initialEstimate' is a list {x, P}, where x is the initial state estimate vector and P is the initial state covariance matrix. \
'measurements' is a list of observed measurement vectors. 
The argument 'system' is a UKFSystem, see UKFSystemQ.";

UKFSmoother::usage = 
"UKFSmoother[initialEstimate, measurements, system] performs both forward Unscented Kalman Filtering (UKF) and backward smoothing using the Rauch-Tung-Striebel (RTS) smoother algorithm. \
'initialEstimate' is a list {x, P}, where x is the initial state estimate vector and P is the initial state covariance matrix. \
'measurements' is a list of observed measurement vectors of the form {time, {__}}. 
The argument 'system' is a UKFSystem, see UKFSystemQ";


Begin["`Private`"]


(* ::Section:: *)
(*Manifolds*)


manifoldDimension[x_] := Length[x \[CircleMinus] x];

(* Default CirclePlus and CircleMinus for numeric values *)
CirclePlus[x:{__?NumericQ}, delta:{__?NumericQ}] := x + delta
CircleMinus[x:{__?NumericQ},    y:{__?NumericQ}] := x - y

(* Thread CirclePlus and CircleMinus over lists *)
CirclePlusPopElement[remainingDelta_, x_] := With[{d = manifoldDimension[x]},  {x \[CirclePlus] Evaluate@Take[remainingDelta, d], Drop[remainingDelta, d]}]
CirclePlus[x_List, delta_] := FoldPairList[CirclePlusPopElement, delta, x]
CircleMinus[x_List, y_List] := Flatten[MapThread[CircleMinus, {x, y}]]

(* Fallback definitions for mismatched types *)
CirclePlus[x_, delta_] := Module[{msg},
  msg = "CirclePlus is not defined for types " <> ToString[Head[x]] <> " and " <> ToString[Head[delta]];
  Message[CirclePlus::undefined, msg];
  Abort[]
]
CircleMinus[x_, y_] := Module[{msg},
  msg = "CircleMinus is not defined for types " <> ToString[Head[x]] <> " and " <> ToString[Head[y]];
  Message[CircleMinus::undefined, msg];
  Abort[]
]

(* Messages *)
CircleMinus::undefined = "`1`";
CircleMinus::undefined = "`1`";


(* ::Section:: *)
(*Sigma Points*)


(* ::Text:: *)
(* Note that the original paper I followed (https://www.dfki.de/fileadmin/user_upload/import/10296_hertzberg_infus_11.pdf  to have a mistake in its sigma-point generation.  For example, it doesn't predict the mean of the square of a normal variable correctly!*)


UKFSigmaPoints[{___, \[Mu]_, P:{{__?NumericQ}..}}, \[CapitalDelta]:{__?NumericQ}, \[Kappa]_?NumericQ] := Module[
  {n, L, xVec, sigmaPointsVec, sigmaPoints, weights, \[Sigma]s},
  n = manifoldDimension[\[Mu]];
  
  If[!PositiveSemidefiniteMatrixQ[P], Abort[]];
  L = CholeskyDecomposition[(n + \[Kappa]) P]; (* Mathematica returns an _upper_ triangular matrix for L. This is what we want anyway, since we want to map across the columns of the lower triangular transpose.*)

  weights = {\[Kappa]/(n + \[Kappa])} ~Join~ ConstantArray[(1/2)/(n + \[Kappa]), 2 n]; 
  \[Sigma]s = {
     \[Mu] \[CirclePlus] \[CapitalDelta],
     \[Mu] \[CirclePlus] (\[CapitalDelta] + #) & /@ L // Splice,
     \[Mu] \[CirclePlus] (\[CapitalDelta] - #) & /@ L // Splice
  };
  
  {\[Sigma]s, weights}
]

defaultSigmaPointK[{___, \[Mu]_, P_}] := 3 - manifoldDimension[\[Mu]] (* n + k = 3 is optimal given a normal distribution. See https://people.eecs.berkeley.edu/~pabbeel/cs287-fa19/optreadings/JulierUhlmann-UKF.pdf *)
UKFSigmaPoints[s_, \[CapitalDelta]:{__?NumericQ}] := UKFSigmaPoints[s, \[CapitalDelta], defaultSigmaPointK[s]] 
UKFSigmaPoints[s:{___, \[Mu]_, P_}] := UKFSigmaPoints[s, ConstantArray[0, manifoldDimension[\[Mu]]], defaultSigmaPointK[s]]

UKFSigmaPointsMean[{\[Sigma]s_, ws_}] := With[{w\[Sigma]s = Length[\[Sigma]s] * ws * \[Sigma]s (* Weighted \[Sigma]s.  Multiply by Length so we can use Mean below *) },	
	FixedPoint[
		\[Mu]i |-> \[Mu]i \[CirclePlus] Mean[(# \[CircleMinus] \[Mu]i) &/@ w\[Sigma]s], (* Using total instead of mean hangs? *)
		First[w\[Sigma]s], 
		SameTest -> (Norm[N[#1-#2]] < 1*^-6 &)
	]
]

UKFSigmaPointsCovariance[{\[Sigma]s_, ws_}, \[Mu]_] := UKFSigmaPointsCrossCovariance[{\[Sigma]s, ws}, {\[Sigma]s, ws}, \[Mu], \[Mu]]
UKFSigmaPointsCovariance[{\[Sigma]s_, ws_}] := UKFSigmaPointsCovariance[{\[Sigma]s, ws}, UKFSigmaPointsMean[{\[Sigma]s, ws}]]

UKFSigmaPointsCrossCovariance[{\[Sigma]sx_, wsx_}, {\[Sigma]sz_, wsz_}, \[Mu]X_, \[Mu]Z_] := With[{
		D = Transpose[\[Sqrt]wsx Map[(# \[CircleMinus] \[Mu]X) &, \[Sigma]sx]],
		E = Transpose[\[Sqrt]wsz Map[(# \[CircleMinus] \[Mu]Z) &, \[Sigma]sz]]
	},
	D . E\[Transpose]
]

UKFSigmaPointsMap[f_, {\[Sigma]s_, ws_}]:= {f/@ \[Sigma]s, ws}
UKFSigmaPointsMap[f_][\[Sigma]s_]:= UKFSigmaPointsMap[f, \[Sigma]s]



(* ::Section:: *)
(*Helpers*)


(* address rounding errors that might make a matrix non-Hermitian*)
makeHermitian[m_]:= 1/2 (m + m\[Transpose]);


stateTime[{t_, __}] := t
measurementTime[{t_, __}] := t
measurementData[{_, x_}] := x 


(* ::Section:: *)
(*Types*)


UKFSystemQ[system_?AssociationQ] := With[{requiredKeys = {
     "ProcessModel",
     "MeasurementModel",
     "ProcessNoise",
     "MeasurementNoise"
     }},
  SubsetQ[Keys[system], requiredKeys] &&
  MatchQ[system["ProcessNoise"], {{__?NumericQ}..}] &&
  MatchQ[system["MeasurementNoise"], {{__?NumericQ}..}]
]


UKFFilterResultsQ[assoc_?AssociationQ] := With[{requiredKeys = {
     "System",
     "FilteredStates"
     }},
  SubsetQ[Keys[assoc], requiredKeys]
]


UKFSmootherResultsQ[assoc_?AssociationQ] := With[{requiredKeys = {
     "System",
     "FilteredStates",
     "SmoothedStates"
     }},
  SubsetQ[Keys[assoc], requiredKeys]
]


(* ::Section:: *)
(*Predict & Update*)


(* UKF Predict Step *)
UKFPredict[state:{t_?NumericQ, x_List, P_List}, \[CapitalDelta]t_?NumericQ, system_?UKFSystemQ] := Module[{f\[Sigma]s, \[Mu], \[CapitalSigma], f, Q},
	f = system["ProcessModel"];
	Q = system["ProcessNoise"];
	f\[Sigma]s = UKFSigmaPointsMap[f[#, \[CapitalDelta]t] /. Lookup[system, "Parameters", {}] &, UKFSigmaPoints[state]]; (* Transformed sigma points *)
	\[Mu] = UKFSigmaPointsMean[f\[Sigma]s]; (* transformed mean *)
	\[CapitalSigma] = makeHermitian[UKFSigmaPointsCovariance[f\[Sigma]s, \[Mu]] + Q]; (* transformed covariance *)
	{t + \[CapitalDelta]t, \[Mu], \[CapitalSigma]}
];
UKFPredict[\[CapitalDelta]t_?NumericQ, system_?UKFSystemQ][state_]:= UKFPredict[state, \[CapitalDelta]t, system];

(* UKF Update Step *)
UKFUpdate[state:{t_, x_, P_}, measurement:{_, z_}, system_?UKFSystemQ] := Module[{\[Sigma]s, h\[Sigma]s, h\[Mu], S, covXZ, K, h, R},
	h = system["MeasurementModel"];
	R = system["MeasurementNoise"];
	\[Sigma]s = UKFSigmaPoints[state];
	h\[Sigma]s = UKFSigmaPointsMap[h[#] /. Lookup[system, "Parameters", {}] &, \[Sigma]s];
	h\[Mu] = UKFSigmaPointsMean[h\[Sigma]s];
	S = UKFSigmaPointsCovariance[h\[Sigma]s, h\[Mu]] + R; (* Total innovation (real measurement - estimated measurement) variance . *)
	covXZ = UKFSigmaPointsCrossCovariance[\[Sigma]s, h\[Sigma]s, x, h\[Mu]]; (* This is roughly how much covariance in the innovation variance is due to state variance *)
	K = covXZ . Inverse[S]; (* Kalman Gain. Intuitively, it weights the innovation by how much of the innovation variance is due to state variance. *)
	(* TODO: Reject outliers? *)
	
	{
		t, 
		UKFSigmaPointsMean@UKFSigmaPoints[state, (* \[CapitalDelta]: *) K . (z - h\[Mu])],
		makeHermitian[P - K . S . K\[Transpose]]
	}
]
UKFUpdate[measurement_, system_?UKFSystemQ][state_] := UKFUpdate[state, measurement, system]


(* ::Section:: *)
(*Filtering*)


UKFFilter[initialEstimate:{t_, x_, P_}, measurements:{__}, system_?UKFSystemQ] := Module[{results, dropInterimStates},
   results = FoldList[
      {state, measurement} |-> With[{\[CapitalDelta]t = measurementTime[measurement] - stateTime[state]},
	      Composition[
	          UKFUpdate[measurement, system],
	          UKFPredict[\[CapitalDelta]t, system]
	      ]@state
	  ],
	  initialEstimate,
	  measurements
   ];
   
   (* If subsequent states have the timestamp, take just the last *)
   dropInterimStates[states_] := Last/@SplitBy[states, N@*stateTime];
   
   <|"System" -> system, "FilteredStates" -> dropInterimStates[results], "Measurements" -> measurements|>
]
UKFFilter[initialEstimate:{t_, x_, P_}, measurements:{__}][system_?UKFSystemQ] := UKFFilter[initialEstimate, measurements, system];


(* ::Section:: *)
(*Smoothing*)


(* ::Text:: *)
(*The way I like to think about the RTS filter is treating the next state as a "measurement." So, for any given state (i), the overall smoother algorithm first predicts the state from state (i-1), then applies a correction given the real measurement at time (i), then\[LongDash]after a little while\[LongDash]applies a correction given the final estimate for the state (i+1).*)
(**)
(*This second step takes a while because we have to finish the forward pass, and then rewind back to state (i). By that time, the estimate we have for state (i+1) will encompass all the measurements\[LongDash]for all times\[LongDash]whereas our regular Kalman estimate for state (i) still only includes earlier times. The question is how to update state (i) given our final distribution for state (i+1). You can derive this directly, but instead, we can reuse a bunch of math if we just pretend it's another measurement.*)
(**)
(*This is mostly straightforward. Start by identifying h with f and R with Q (i.e., we map our state to the "measurement" by predicting the next step). That gives an analog of the Kalman gain. (There is a shortcut here, in that we have already calculated the total covariance of the "measurement"\[LongDash]it was the prediction for step (i+1) during the forward Kalman pass.)*)
(**)
(*To get the mean of our updated distribution, we just use the same equation as the regular Kalman correction, but using the new gain and the mean of state (i+1) instead of the measurement. Using the mean here reveals one additional complication\[LongDash]a measurement is a single value; state (i+1) is a distribution. But this turns out to be easy to deal with: just use the mean of state (i+1) as the measurement, and add the covariance of state (i+1) to the updated variance.  (This latter can be derived from the law of total variance \[Dash] although we must assume that the covariance of the mean of state (i) does not depend on actual value of state (i+1)).*)


(* Returns parameters of the joint distribution Subscript[x, i] and Subscript[x, i+1] conditioned over all the data. This is part of the backwards update of the RTS algorithm where a filtered
state is smoothed by the future data.  The returned parameters are given as {{Subscript[t, i], Subscript[t, i+1]}, {Subscript[\[Mu], i], Subscript[\[Mu], i+1]}, {{Subscript[V, i,i], Subscript[V, i,i+1], Subscript[V, i+1,i+1]}}.  
Note that the covariance between the states, Subscript[V, i,i+1], is returned: this is useful for parameter estimation. *)
(* NB: Could be optimized by saving the sigma points from the forward pass!*)
UKFBackwardsUpdateTransition[state:{t1_, x_, P_}, subsequentState:{t2_, \[DoubleStruckX]_, \[DoubleStruckCapitalP]_}, system_?UKFSystemQ]:=Module[{\[Sigma]s, f\[Sigma]s, f\[Mu], covXZ, S, C, F, \[CapitalDelta]t, f, Q, X},
	f = system["ProcessModel"];
	Q = system["ProcessNoise"];
	\[CapitalDelta]t = t2 - t1;
	\[Sigma]s = UKFSigmaPoints[state]; 
	f\[Sigma]s = UKFSigmaPointsMap[f[#, \[CapitalDelta]t] /. Lookup[system, "Parameters", {}] &, \[Sigma]s];
	f\[Mu] = UKFSigmaPointsMean[f\[Sigma]s];
	S = UKFSigmaPointsCovariance[f\[Sigma]s, f\[Mu]] + Q;
	covXZ = UKFSigmaPointsCrossCovariance[\[Sigma]s, f\[Sigma]s, x, f\[Mu]];
	C = covXZ . Inverse[S];
	
	{
	    {t1, t2},
		{UKFSigmaPointsMean@UKFSigmaPoints[state, C . (\[DoubleStruckX] - f\[Mu])], \[DoubleStruckX]},
		{makeHermitian[P + C . (\[DoubleStruckCapitalP] - S) . C\[Transpose]], C . \[DoubleStruckCapitalP], \[DoubleStruckCapitalP]}
	}
];

UKFBackwardsUpdate[state:{t1_, x_, P_}, subsequentState:{t2_, \[DoubleStruckX]_, \[DoubleStruckCapitalP]_}, system_?UKFSystemQ] := UKFBackwardsUpdateTransition[state, subsequentState, system][[All,1]]

 
UKFSmoother[filterResults_?UKFFilterResultsQ] := Module[{system, forwardPass, backwardPass},
	system = filterResults["System"];
   forwardPass = filterResults["FilteredStates"];
 
   backwardPass = FoldList[
      {nextState, state} |-> UKFBackwardsUpdate[state, nextState, system],
	  Last[forwardPass],
	  Rest[Reverse[forwardPass]]
   ];
   
   Append[filterResults, "SmoothedStates" -> Reverse[backwardPass]]
]


(* ::Section:: *)
(*Parameter Estimation*)


(* ::Text:: *)
(*Estimate the parameters of the filter using expectation maximization. See "Documentation/English/Kalman Parameter Estimation"*)


(* The purpose of this function is to make a list of {x:{__}, y:{__}} that the nonlinear fitting procedure will use when trying to do f[x] = y *)
makeTransitionDataForFit[parameters_, estimates_?UKFSmootherResultsQ] := Module[{system, makeSigmaPointsFromTransition, \[CapitalDelta]ts},
	system = estimates["System"];
	
	If[!TrueQ[Length[estimates["SmoothedStates"]] > 0], Return[system]];
	n = manifoldDimension[First[estimates["SmoothedStates"]][[2]]];
	
	(* Find the sigma points represnting the joint distribution of the states at the start & end of the transition *);
	makeSigmaPointsFromTransition[{times_, means_, covars_}] := UKFSigmaPoints[{
		Flatten[means, 1],	
		ArrayFlatten[{
			{covars[[1]], covars[[2]]},
			{covars[[2]]\[Transpose], covars[[3]]}
		}]
	}, 
	ConstantArray[0, 2 n],
	1 (* THis is to avoid negative weights! That doesn't play well with our extension to nonlinear maximization. I don't think this will make a big difference, but we might be able to work around it when moving to c.*)
	];
	
	(* Duration of all the transitions *);
	\[CapitalDelta]ts = Map[stateTime[#[[2]]] - stateTime[#[[1]]] &,  Partition[estimates["SmoothedStates"], 2, 1]];
	
	Composition[
		Flatten[#, 1] &,
		
		(* Add in the duration of each transition. This is needed to use use the process model function. *)
		MapThread[{\[CapitalDelta]t, vars} |-> MapAt[Prepend[\[CapitalDelta]t], vars, {All, 1}] , {\[CapitalDelta]ts, #}] &,
		
		Map[Composition[
			(* Split each sigma point in half. The first is the "x" in the nonlinear fit, the second half is the "y". We plan to fit f[x] = y *)
			#[[1]] * Sqrt[#[[2]]]&, (* Weight each {x, y} point for the nonlinear fit. Note the Sqrt which is required for the estimated value to be correct*)
			UKFSigmaPointsMap[TakeDrop[#, n] &], (* Each sigma point is mapped to {{Subscript[\[Sigma]z, i]..}, {Subscript[\[Sigma]z, i+1]..}}.  For the nonlinear fit, this is {{x}, {y}} *)
			
			(* Create sigma points for the joint transition *)
			makeSigmaPointsFromTransition,
			UKFBackwardsUpdateTransition[#[[1]], #[[2]], system] &
		]],
		
		(* Pair up filtered states with their succeeding smoothed state *)
		Transpose[{Most[#"FilteredStates"], Rest[#"SmoothedStates"]}] & 
	]@estimates
]


(* The purpose of this function is to make a list of {x:{__}, y:{__}} that the nonlinear fitting procedure will use when trying to do f[x] = y *)
makeMeasurementDataForFit[parameters_, estimates_?UKFSmootherResultsQ] := Module[{system, dataForMeasurement},
	system = estimates["System"];
	
	(* Get a list of sigma points corresponding to a measurement *)
	dataForMeasurement[measurement_] := Composition[
		(* The transition fit data will have a \[CapitalDelta]t prepended to it. That doesn't apply to measurement fit data, but we still need to add a placeholder value there. The NonlinearModelFit we use isn't aware that there are two different kinds of data *)
		MapAt[Prepend[-1], {All, 1}],
		
		(* Weight each {x, y} pair using the sigma point weights \[Dash] similar to what we did for transitions *)
		#[[1]] * Sqrt[#[[2]]]&,
		
		(* Each sigma point will be used as {x, y} data in the fit: map over each sigma point to append the measurement. *)
		UKFSigmaPointsMap[{#, measurementData[measurement]} &],

		(* Get the state corresponding to this measurement and make a set of sigma points for it *)
		UKFSigmaPoints[#, ConstantArray[0, manifoldDimension[#[[2]]]], 1] &,
		SelectFirst[stateTime[#] == measurementTime[measurement] &]	
	]@estimates["SmoothedStates"];
	
	Flatten[dataForMeasurement /@ estimates["Measurements"], 1]
]


UKFParameterMaximization[parameters_, estimates_?UKFSmootherResultsQ] := Module[{f, h, Q, R, system, transitionFitData, measurementFitData, \[CapitalDelta]ts, makeSigmaPointsFromTransition, n, xStateSymbols, xSymbols, fit, bestFitParameters, makeFitDataForMeasurement, allFitData, weights},
	system = estimates["System"];
	f = system["ProcessModel"];
	h = system["MeasurementModel"];
	Q = system["ProcessNoise"];
	R = system["MeasurementNoise"];
	
	If[!TrueQ[Length[estimates["SmoothedStates"]] > 0], Return[system]];
	n = manifoldDimension[First[estimates["SmoothedStates"]][[2]]];
	
	transitionFitData = makeTransitionDataForFit[parameters, estimates];
	
	measurementFitData = makeMeasurementDataForFit[parameters, estimates];
	
	(* We use index \[FormalJ] for transition vs measurement data. 1 for transition, 2 for measurement. We also have already prepended time to transition data, so we must append a placeholder to the measurement data as well so that our x values match *);
	allFitData = Join[MapAt[Prepend[1], transitionFitData, {All, 1}], MapAt[Prepend[2], measurementFitData, {All, 1}]];
	
	xStateSymbols = Table[Symbol["\[FormalX]"<>ToString[i]], {i, n}];
	xSymbols = {\[FormalJ], \[FormalT]} ~Join~ xStateSymbols;
	
	weights = ConstantArray[Q, Length@transitionFitData] ~Join~ ConstantArray[R, Length@measurementFitData];
	
	fit = MultiNonlinearFitModelFit[allFitData, weights, {f[xStateSymbols, \[FormalT]], h[xStateSymbols]}[[\[FormalJ]]], parameters, xSymbols];
	bestFitParameters = EchoLabel["Best Fit Params"]@fit["BestFitParameters"];
	Association[system, "Parameters" -> bestFitParameters]
]


(* ::Text:: *)
(*Mathematica's NonlinearModelFit assumes the y's are scalars. This method extends them to be vectors. It attempts to find parameters that minimize \!\(\*UnderscriptBox[\(\[CapitalSigma]\), \(i\)]\) (Subscript[y, i] - f(x))\[Transpose] . Q^-1(Subscript[y, i ]- f(x)).  To do  this, we flatten out the elements of y into individual data points . We must also add an "index" independent variable so we know what element to take of the function we're fitting . *)


MultiNonlinearFitModelFit::usage = "
MultiNonlinearFitModelFit[data, weights, form, params, xSymbols] extends NonlinearModelFit to handle the case that the \!\(\*SubscriptBox[\(y\), \(i\)]\) are vectors. It attempts to find parameters that minimize \!\(\*FormBox[\(\*UnderscriptBox[\(\[CapitalSigma]\), \(i\)]\\\ \((\*SubscriptBox[\(y\), \(i\)]\\\  - \\\ f(x))\)\[Transpose]  . \(\*SuperscriptBox[SubscriptBox[\(Q\), \(i\)], \(-1\)](\*SubscriptBox[\(y\), \(i\(\\\ \)\)] - \\\ f(x))\)\),
TraditionalForm]\) where \!\(\*SubscriptBox[\(Q\), \(i\)]\) is a positive definite weight matrix.
data should be of the form {{\!\(\*SubscriptBox[\(x\), \(1\)]\), \!\(\*SubscriptBox[\(x\), \(2\)]\), ...}, {\!\(\*SubscriptBox[\(y\), \(1\)]\), \!\(\*SubscriptBox[\(y\), \(2\)]\), ...}}
";
MultiNonlinearFitModelFit::QNotDiagonal = "Q is currently assumed to be a diagonal matrix";
MultiNonlinearFitModelFit::QNotPositiveDefinite = "Q must be postive definite";
MultiNonlinearFitModelFit[data_, weights_, form_, params_, xSymbols_] := Module[{destructure, destructuredData, augmentedX, flattenedWeights},
	If[!AllTrue[weights, PositiveDefiniteMatrixQ], Message[MultiNonlinearFitModelFit::QNotPositiveDefinite]; Abort[]];
	
	(* Nonlinear fit assumes scalar y's. To get around this, we flatten out the elements of y into individual data points. We must also add an "index" independent variable so we know what element to take of the function we're fitting. *)
	destructure[{x_, y_}] := MapIndexed[Prepend[First[#2]][x] -> #1 &, y];
	destructuredData = Flatten[destructure /@ data];
	
	(* Flatten the weights too *)
	(* Currently we assume that all the Q is diagonal. If we need to relax this, we can use SVD to break apart Q *)
	If[!AllTrue[weights, DiagonalMatrixQ], Message[MultiNonlinearFitModelFit::QNotDiagonal]; Abort[]];
	flattenedWeights = Flatten[Map[1./Diagonal[#] &, weights]];
	
	augmentedX = {\[FormalI]} ~Join~ xSymbols;
	
	NonlinearModelFit[destructuredData, form[[\[FormalI]]], params, augmentedX, Weights -> flattenedWeights]
]


(* ::Section:: *)
(*Package Footer*)


End[] (* End `Private` *)

EndPackage[]
