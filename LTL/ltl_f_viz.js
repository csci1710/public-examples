/*
  Visualizing LTLf formulas and finite traces
  (This visualizer relies on the definitions in ltl_f.frg)

  Since this example is meant to drive improvements to script view, I'm taking notes on 
  various issues encountered during development. High level concerns include:
    * no typescript
    * (as of yet) no forge-style errors on e.g. empty join
    * the editing experience is quite bad, since one has to keep copypasting from a "real" editor
    * accessibility concerns (e.g. zoom in, or open web dev console)
    * there's no way to change the size of the SVG subwindow to make more room for the editor
    * there's no docs links for the library functions

    * It's really, really easy to mix up here:
      "the atom State0" and "the singleton set State0"
*/

const stage = new Stage()

  // ? how to render transition arrows between states? 
  // ? Call to Function() blocked by CSP: reload Sterling page

const formulas = [...Binary.atoms(), ...Unary.atoms(), ...Atom.atoms()]
const traces = [...Trace.atoms()]

////////////////////
// Formulas
////////////////////

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
        return `${f}`.replace("Formula", "")
    }
    return `(unknown formula type)`
  }
  
  // Formulas.atoms() will be empty, since
  // an atom appears in the _lowest-level_ sig it belongs to.
  // Don't confuse "Atom" and atom()
  const formulaStrings = formulas.map(formula2String)
  
  // TODO: this should be more sophisticated
  //   10 isn't enough for atoms
  const CHARWIDTH = 7
  const horzFormulaSize = Math.max(...formulaStrings.map(s => s.length)) * CHARWIDTH
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
        y_size:formulas.length+1,
        x_size:3
    }
  }

  function traceStatePair2String(pair) {      
      t = pair.atoms()[0]
      s = pair.atoms()[1]
      traceStates = trace2States(t)
      
      
      // EXAMPLE: debugging without console to help determine types
      //   since console shows proxies, which is very confusing
    //   stage.add(new TextBox(`${Object.keys(s)}`,{x:100, y:100},'black',16)); 
    //   stage.add(new TextBox(`${Object.keys(t)}`,{x:100, y:150},'black',16)); 
    //   stage.add(new TextBox(`${traceStates}`,{x:100, y:200},'black',16)); 
    //   stage.add(new TextBox(`${traceStates.map(x => Object.keys(x))}`,{x:100, y:250},'black',16));     
      
      return `${traces.indexOf(t)}@${traceStates.indexOf(s)}`
  }
    
  const formulaGrid = new Grid(formulaGridConfig)
  formulaGrid.add({x:0, y:0}, new TextBox(`Fmla ID`,{x:0,y:0},'black',16))
  formulaGrid.add({x:1, y:0}, new TextBox(`Syntax`,{x:0,y:0},'black',16))
  formulaGrid.add({x:2, y:0}, new TextBox(`True in...`,{x:0,y:0},'black',16))

  formulaStrings.forEach( (fstr,i) => {                 
          const label = `${fstr}`
          formulaGrid.add({x:0, y:i+1}, new TextBox(`${i}`,{x:0,y:0},'black',16)); 
          formulaGrid.add({x:1, y:i+1}, new TextBox(label,{x:0,y:0},'black',16)); 
  })
  
  formulas.forEach( (f, i) => {
      const whereTrue = Semantics.table.join(f).tuples()
      const label = `[${whereTrue.map(traceStatePair2String)}]`
      formulaGrid.add({x:2, y:i+1}, new TextBox(label,{x:0,y:0},'black',16)); 

  })
  
  ////////////////////
  // TRACES
  ////////////////////
  const maxTraceLength = Math.max(...traces.map(t => t.next.tuples().length + 1))
  
  const traceGridConfig = {
    grid_location :{
        x:10,
        // TODO: should be calculated (grid within grid?)
        y:400
    },
    cell_size:{
        x_size:100,
        y_size:70
    },
    grid_dimensions:{
        y_size:traces.length+1,
        x_size:maxTraceLength+2
    }
  }

  // For debugging and lightweight viz
  function state2String(s) {
      // TODO This produced 'undefined' -- proxy failure
      // return `${s}: ${s.truths}`
      const trueAtoms = s.join(truths).tuples()
      return `[${trueAtoms.map(formula2String)}]`             
  }
  // Produce a list of state atoms in the trace, ordered
  function trace2States(t) {
        states = []
        var todo = t.first
        while(!todo.empty()) {
            // NOTE WELL:
            // todo is an expression
            // todo.tuples() is an array of AlloyTuple
            // todo.tuples()[0].atoms() is an array of AlloyAtom
            states.push(todo.tuples()[0].atoms()[0])
            todo = todo.join(t.next)
        }            
        return states
  }

  function state2Shape(s) {
      const trueAtomsStrs = `[${s.join(truths).tuples().map(formula2String)}]`
      const label = new TextBox(trueAtomsStrs,{x:0,y:0},'black',16)
      const circle = new Circle(30,{x:0,y:0},"white",2,"black")
      const result = new ConjoinedObject()
      result.add(circle)
      result.add(label)
      
      return result
  }
  function trace2ShapeArray(t) {
      const states = trace2States(t)
      return states.map(state2Shape)
  }
  
  const traceGrid = new Grid(traceGridConfig)
  traceGrid.hide_grid_lines()

  for(i = 0;i<maxTraceLength;i++) {
    traceGrid.add({x:i+1, y:0}, new TextBox(`t=${i}`,{x:0,y:0},'black',16))
  }

  traces.forEach( (t,traceIdx) => 
      {
          traceGrid.add({x:0, y:traceIdx+1}, new TextBox(`Tr${traceIdx}`,{x:0,y:0},'black',16)); 
          const stateShapes = trace2ShapeArray(t)
          stateShapes.forEach( (stateShape, stateIdx) => {
            traceGrid.add({x:stateIdx+1, y:traceIdx+1}, stateShape); 
          })
          
      }
  )
  

  stage.add(formulaGrid)
  stage.add(traceGrid)
  stage.render(svg, document)
  
  
  // Kinda want a "what sterlingType is this" field
  //  if it has .atoms() and .tuples(), it is an AlloyTuple
  //  if it has .tuples() and .id(), it is an AlloyAtom
  
  
  
  
  