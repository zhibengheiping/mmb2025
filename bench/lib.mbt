pub fn sqrt(x: Double) -> Double {
  return x.sqrt()
}

pub fn sin(x: Double) -> Double {
  return @math.sin(x)
}

pub fn cos(x: Double) -> Double {
  return @math.cos(x)
}

pub fn atan(x: Double) -> Double {
  return @math.atan(x)
}

pub fn float_of_int(x: Int) -> Double {
  return x.to_double()
}

pub fn int_of_float(x: Double) -> Int {
  return x.to_int()
}

pub fn print_int(x: Int) -> Unit {
  println(x)
}

pub extern "C" fn read_int() -> Int = "minimbt_read_int"
