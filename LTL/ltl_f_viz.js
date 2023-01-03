/*
  Visualizing LTLf formulas and finite traces
  (This visualizer relies on the definitions in ltl_f.frg)
*/


////////////////////
// Formulas
////////////////////

console.log(1)

function formula2String(f) {
  if(f.in(Unary)) {
      if(f.uop.in(Not))        return `not(${formula2String(f.sub)})`
      if(f.uop.in(Eventually)) return `eventually(${formula2String(f.sub)})`
      if(f.uop.in(Always))     return `always(${formula2String(f.sub)})`
      if(f.uop.in(Next))       return `next_state(${formula2String(f.sub)})`
      else return `(unknown unary formula)`
  }
  if(f.in(Binary)) {
      if(f.bop.in(And))   return `(${formula2String(f.left)} and ${formula2String(f.right)})`
      if(f.bop.in(Or))    return `(${formula2String(f.left)} or ${formula2String(f.right)})`
      if(f.bop.in(Until)) return `(${formula2String(f.left)} until ${formula2String(f.right)})`
      else return `(unknown unary formula)`
  }
  if(f.in(Atom)) {
      return `${f}`.replace("[Formula", "").replace("]", "")
  }
  return `(unknown formula type)`
}
console.log(2)
// Formulas.atoms() will be empty, since
// an atom appears in the _lowest-level_ sig it belongs to.
// Don't confuse "Atom" and atom()
const formulas = [...Binary.atoms(), ...Unary.atoms(), ...Atom.atoms()]
const formulaStrings = formulas.map(formula2String)

console.log(formulas)
console.log(formulaStrings)
console.log(formulas.map(formula2String))
// TODO: this should be more sophisticated
const horzFormulaSize = Math.max(...formulaStrings.map(s => s.length)) * 10
console.log(3)
const formulaGridConfig = {
  grid_location :{
      x:10,
      y:10
  },
  cell_size:{
      x_size:horzFormulaSize,
      y_size:40
  },
  grid_dimensions:{
      y_size:formulas.length,
      x_size:1
  }
}
console.log(formulaStrings)
console.log(formulas)

const formulaGrid = new Grid(formulaGridConfig)
formulaStrings.forEach( (fstr,i) => 
    {         
        console.log(typeof(fstr)) 
        try {
            formulaGrid.add({x:0, y:i}, new TextBox(fstr,{x:0,y:0},'black',16)); 
        } catch(e) {
            // TODO: custom error is being suppressed by error branch changes
            console.log(e)
        }
    }
)
console.log(100)

////////////////////
// TRACES
////////////////////
const traces = [...Trace.atoms()]

const traceGridConfig = {
  grid_location :{
      x:10,
      // TODO: should be calculated (grid within grid?)
      y:400
  },
  cell_size:{
      x_size:100,
      y_size:40
  },
  grid_dimensions:{
      y_size:traces.length,
      x_size:1
  }
}

console.log(3)
const traceGrid = new Grid(traceGridConfig)
traces.forEach( (t,i) => 
    {          
        traceGrid.add({x:0, y:i}, new TextBox(t,{x:0,y:0},'black',16)); 
    }
)


console.log(4)
const stage = new Stage()
stage.add(formulaGrid)
stage.add(traceGrid)
stage.render(svg, document)
console.log(5)








