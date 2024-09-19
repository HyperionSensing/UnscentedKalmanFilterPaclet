(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["UnscentedKalmanFilter`"]

UKFPredict::usage = 
"UKFPredict[state, system] performs the prediction step of the Unscented Kalman Filter (UKF). \
The argument 'state' is a list {x, P}, where x is the current state estimate and P is the current state covariance matrix. \
The argument 'system' is a list {f, h, Q, R}, where f[\[CapitalDelta]t, state] is the process model function (state transition function), h is the measurement model function (included for consistency), Q is the process noise covariance matrix, and R is the measurement noise covariance matrix (included for consistency).";

UKFUpdate::usage = 
"UKFUpdate[state, z, system] performs the update step of the Unscented Kalman Filter (UKF). \
The argument 'state' is a list {x, P}, where x is the predicted state estimate and P is the predicted state covariance matrix. \
'z' is the measurement vector of the form {time, {__}}. 'system' is a list {f, h, Q, R}, where f[\[CapitalDelta]t, state] is the process model function (included for consistency), h is the measurement model function, Q is the process noise covariance matrix (included for consistency), and R is the measurement noise covariance matrix.";

UKFFilter::usage = 
"UKFFilter[initialEstimate, measurements, system] performs Unscented Kalman Filtering (UKF) to estimate the state of a dynamic system over time. \
'initialEstimate' is a list {x, P}, where x is the initial state estimate vector and P is the initial state covariance matrix. \
'measurements' is a list of observed measurement vectors. 'system' is a list {f, h, Q, R}, where f[\[CapitalDelta]t, state] is the state transition function, h is the measurement function, Q is the process noise covariance matrix, and R is the measurement noise covariance matrix.";

UKFSmoother::usage = 
"UKFSmoother[initialEstimate, measurements, system] performs both forward Unscented Kalman Filtering (UKF) and backward smoothing using the Rauch-Tung-Striebel (RTS) smoother algorithm. \
'initialEstimate' is a list {x, P}, where x is the initial state estimate vector and P is the initial state covariance matrix. \
'measurements' is a list of observed measurement vectors of the form {time, {__}}. 'system' is a list {f, h, Q, R}, where f[\[CapitalDelta]t, state] is the state transition function, h is the measurement function, Q is the process noise covariance matrix, and R is the measurement noise covariance matrix.";


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


(* Generate sigma points for the UKF *)
generateSigmaPoints[{t_, \[Mu]_,  P_}, \[CapitalDelta]_List] := Module[
  {n, L, xVec, sigmaPointsVec, sigmaPoints},
  
  If[!PositiveSemidefiniteMatrixQ[P], Abort[]];
  L = CholeskyDecomposition[P]; (* Mathematica returns an _upper_ triangular matrix for L. This is what we want anyway, since we want to map across the columns of the lower triangular transpose.*)

  {
     \[Mu] \[CirclePlus] \[CapitalDelta],
     \[Mu] \[CirclePlus] (\[CapitalDelta] + #) & /@ L // Splice,
     \[Mu] \[CirclePlus] (\[CapitalDelta] - #) & /@ L // Splice
  }
]

generateSigmaPoints[state:{t_, \[Mu]_, P_}] := generateSigmaPoints[state, ConstantArray[0, manifoldDimension[\[Mu]]]];

sigmaPointsMean[\[Sigma]s_] := FixedPoint[
	\[Mu]i |-> \[Mu]i \[CirclePlus] Mean[(# \[CircleMinus] \[Mu]i) &/@ \[Sigma]s], 
	First[\[Sigma]s], 
	SameTest -> (Norm[N[#1-#2]] < 1*^-6 &)
	];

sigmaPointsCovariance[\[Sigma]s_, \[Mu]_] := With[
	{
		D = Transpose[(# \[CircleMinus] \[Mu]) & /@ \[Sigma]s]
	},
	
   1/2 D . D\[Transpose]
]

sigmaPointsCrossCovariance[\[Sigma]s_, z_, \[Mu]X_, \[Mu]Z_] := With[
	{
		D = Transpose[(# \[CircleMinus] \[Mu]X) & /@ \[Sigma]s], 
		E = Transpose[(# \[CircleMinus] \[Mu]Z )& /@ z]
	},
	
   1/2 D . E\[Transpose]
]

applyDelta[{t_, x_, P_}, \[CapitalDelta]_]:= sigmaPointsMean[generateSigmaPoints[{t, x, P}, \[CapitalDelta]]]


(* ::Section:: *)
(*Helpers*)


(* address rounding errors that might make a matrix non-Hermitian*)
makeHermitian[m_]:= 1/2 (m + m\[Transpose]);


stateTime[{t_, __}] := t
measurementTime[{t_, __}] := t


(* ::Section:: *)
(*Predict & Update*)


(* UKF Predict Step *)
UKFPredict[state:{t_?NumericQ, x_List, P_List}, \[CapitalDelta]t_?NumericQ, system:{f_, h_, Q_, R_}] := Module[{f\[Sigma]s, \[Mu], \[CapitalSigma]},
	f\[Sigma]s = OperatorApplied[f][\[CapitalDelta]t] /@ generateSigmaPoints[state]; (* Transformed sigma points *)
	\[Mu] = sigmaPointsMean[f\[Sigma]s]; (* transformed mean *)
	\[CapitalSigma] = makeHermitian[sigmaPointsCovariance[f\[Sigma]s, \[Mu]] + Q]; (* transformed covariance *)
	{t + \[CapitalDelta]t, \[Mu], \[CapitalSigma]}
];
UKFPredict[\[CapitalDelta]t_?NumericQ, system:{f_, h_, Q_, R_}][state_]:= UKFPredict[state, \[CapitalDelta]t, system];

(* UKF Update Step *)
UKFUpdate[state:{t_, x_, P_}, measurement:{_, z_}, system:{f_, h_, Q_, R_}] := Module[{\[Sigma]s, h\[Sigma]s, h\[Mu], S, covXZ, K},
	\[Sigma]s = generateSigmaPoints[state];
	h\[Sigma]s = h /@ \[Sigma]s;
	h\[Mu] = sigmaPointsMean[h\[Sigma]s];
	S = sigmaPointsCovariance[h\[Sigma]s, h\[Mu]] + R; (* Total innovation (real measurement - estimated measurement) variance . *)
	covXZ = sigmaPointsCrossCovariance[\[Sigma]s, h\[Sigma]s, x, h\[Mu]]; (* This is roughly how much covariance in the innovation variance is due to state variance *)
	K = covXZ . Inverse[S]; (* Kalman Gain. Intuitively, it weights the innovation by how much of the innovation variance is due to state variance. *)
	(* TODO: Reject outliers? *)
	
	{
		t, 
		applyDelta[state, K . (z - h\[Mu])],
		makeHermitian[P - K . S . K\[Transpose]]
	}
]
UKFUpdate[measurement_, system:{f_, h_, Q_, R_}][state_]:= UKFUpdate[state, measurement, system]


(* ::Section:: *)
(*Filtering*)


UKFFilter[initialEstimate:{t_, x_, P_}, measurements:{__}, system:{f_, h_, Q_, R_}] := 
   FoldList[
      {state, measurement} |-> With[{\[CapitalDelta]t = measurementTime[measurement] - stateTime[state]},
	      Composition[
	          UKFUpdate[measurement, system],
	          UKFPredict[\[CapitalDelta]t, system]
	      ]@state
	  ],
	  initialEstimate,
	  measurements
   ]


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


(* Could be optimized by saving the sigma points from the forward pass!*)
UKFBackwardsUpdate[state:{t1_, x_, P_}, nextState:{t2_, \[DoubleStruckX]_, \[DoubleStruckCapitalP]_}, system:{f_, h_, Q_, R_}]:=Module[{\[Sigma]s, f\[Sigma]s, f\[Mu], covXZ, S, C, F, \[CapitalDelta]t},
	\[CapitalDelta]t = t2 - t1;
	\[Sigma]s = generateSigmaPoints[state]; 
	f\[Sigma]s = OperatorApplied[f][\[CapitalDelta]t] /@ \[Sigma]s;
	f\[Mu] = sigmaPointsMean[f\[Sigma]s];
	S = sigmaPointsCovariance[f\[Sigma]s, f\[Mu]] + Q;
	covXZ = sigmaPointsCrossCovariance[\[Sigma]s, f\[Sigma]s, x, f\[Mu]];
	C = covXZ . Inverse[S];
	
	{
	    t1,
		applyDelta[state, C . (\[DoubleStruckX] - f\[Mu])],
		makeHermitian[P + C . (\[DoubleStruckCapitalP] - S) . C\[Transpose]]
	}
];
 
UKFSmoother[initialEstimate:{t_, x_, P_}, measurements:{__}, system:{f_, h_, Q_, R_}] := Module[{intialUpdatedEstimate, forwardPass, backwardPass, forwardPassStates, ForwardPassPredictions, reversePassInput},
   intialUpdatedEstimate = UKFUpdate[initialEstimate, First[measurements], system];
  
   forwardPass = UKFFilter[initialEstimate, measurements, system];
 
   backwardPass = FoldList[
      {nextState, state} |-> UKFBackwardsUpdate[state, nextState, system],
	  Last[forwardPass],
	  Rest[Reverse[forwardPass]]
   ];
   
   Reverse[backwardPass]
]


(* ::Section:: *)
(*Package Footer*)


End[] (* End `Private` *)

EndPackage[]
