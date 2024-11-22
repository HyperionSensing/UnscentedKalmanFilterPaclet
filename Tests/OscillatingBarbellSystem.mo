model IMUSensor "An extension of AbsoluteSensor that also measures proper acceleration"
  extends Modelica.Mechanics.MultiBody.Sensors.AbsoluteSensor(get_a = true);
  import Modelica.Mechanics.MultiBody.*;

  // Outputs
  // Proper Acceleration
  output Real pa[3](unit = "m/s2");

equation
  pa = a + Frames.resolve2(frame_a.R, {0, 9.81, 0});
end IMUSensor;

model OscillatingBarbell "A barbell that can rotate around one axis with sinusoidal torque"
  extends Modelica.Icons.Example;
  import Modelica.Mechanics.MultiBody.*;
  import Modelica.Blocks.Sources.Sine;
  import Modelica.Mechanics.Rotational.Sources.Torque;

  parameter Real length = 1.0;

  // The default gravity does not show up on the accelerometer readings. So we artificially accelerate upwards.


  inner World world(gravityType = Modelica.Mechanics.MultiBody.Types.GravityTypes.NoGravity) 
    annotation(Placement(transformation(extent = {{-60, 0}, {-40, 20}}, origin = {10, -10})));

  // Moving body to simulate upward acceleration
  Parts.PointMass movingBody(m = 1.0) 
    annotation(Placement(transformation(extent = {{-60, -20}, {-40, 0}}, origin = {10, -10})));

  Joints.Revolute rev(n = {0, 1, 0}, useAxisFlange = true, phi(fixed = true), w(fixed = true)) 
    annotation(Placement(transformation(extent = {{-20, 0}, {0, 20}}, origin = {10, -10})));

  Sine sinTorque(amplitude = 10, f = 1, startTime = 0) 
    annotation(Placement(transformation(extent = {{-60, 20}, {-40, 40}}, origin = {10, -10})));

  Torque torqueSource(tau = sinTorque.y) 
    annotation(Placement(transformation(extent = {{-40, 0}, {-20, 20}}, origin = {10, -10})));

  Parts.FixedTranslation translation1(r = {3 *length/4, 0, 0}) 
    annotation(Placement(transformation(extent = {{0, 0}, {20, 20}}, origin = {10, -10})));

  Parts.PointMass body1(m = 1.0) 
    annotation(Placement(transformation(extent = {{40, 0}, {60, 20}}, origin = {10, -10})));

  IMUSensor sensor1(get_a = true, get_w = true, get_z = true)
    annotation(Placement(transformation(extent = {{40, 20}, {60, 40}}, origin = {10, -10})));

  Parts.FixedTranslation translation2(r = {-length/4, 0, 0}) 
    annotation(Placement(transformation(extent = {{0, 0}, {20, 20}}, origin = {10, -10})));

  Parts.PointMass body2(m = 1.0) 
    annotation(Placement(transformation(extent = {{40, 0}, {60, 20}}, origin = {40, -10})));

  IMUSensor sensor2(get_a = true, get_w = true, get_z = true)
    annotation(Placement(transformation(extent = {{40, 20}, {60, 40}}, origin = {40, -10})));

equation

  connect(world.frame_b, rev.frame_a) 
    annotation(Line(points = {{-40, 10}, {-20, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(torqueSource.flange, rev.axis) 
    annotation(Line(points = {{-30, 10}, {-10, 10}}, color = {0, 0, 255}));

  connect(translation1.frame_a, rev.frame_b) 
    annotation(Line(points = {{0, 10}, {-20, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(body1.frame_a, translation1.frame_b) 
    annotation(Line(points = {{40, 10}, {20, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(sensor1.frame_a, body1.frame_a) 
    annotation(Line(points = {{50, 20}, {50, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(translation2.frame_a, rev.frame_b) 
    annotation(Line(points = {{0, 10}, {-20, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(body2.frame_a, translation2.frame_b) 
    annotation(Line(points = {{40, 10}, {20, 10}}, color = {95, 95, 95}, thickness = 0.5, origin = {10, -10}));

  connect(sensor2.frame_a, body2.frame_a);

end OscillatingBarbell;