default Order dec
$include <prelude.sail>


val main: unit -> unit

val trial: unit -> unit

function trial() =
{

let x : int = 10;
var y : int = 2;
y = x + x;
}
 
val sum: forall 'x 'y.
 (int('x), int('y)) -> int

function sum(x, y) =
{
var z : int = 0;
z = x + y;
z  
}   


function main() =
{

trial();
let k = sum(1, 2);


let x : int = 10;
var y : int = 2;
y = x + x;

}
