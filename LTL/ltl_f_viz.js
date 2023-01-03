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
*/


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
  const formulas = [...Binary.atoms(), ...Unary.atoms(), ...Atom.atoms()]
  const formulaStrings = formulas.map(formula2String)
  
  // TODO: this should be more sophisticated
  //   10 isn't enough for atoms
  const CHARWIDTH = 12
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
        y_size:formulas.length,
        x_size:1
    }
  }
  
  const formulaGrid = new Grid(formulaGridConfig)
  formulaStrings.forEach( (fstr,i) => 
      {                 
          const label = `${i}: ${fstr}`
          formulaGrid.add({x:0, y:i}, new TextBox(label,{x:0,y:0},'black',16)); 
      }
  )
  
  ////////////////////
  // TRACES
  ////////////////////
  const traces = [...Trace.atoms()]
  const maxTraceLength = Math.max(...traces.map(t => t.next.tuples().length))
  
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
        y_size:traces.length,
        x_size:maxTraceLength+1
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
        var todo = t.first.tuples()[0]
        while(!todo.empty()) {
            states.push(todo)
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
  traces.forEach( (t,traceIdx) => 
      {
          const stateShapes = trace2ShapeArray(t)
          stateShapes.forEach( (stateShape, stateIdx) => {
            traceGrid.add({x:stateIdx, y:traceIdx}, stateShape); 
          })
          
      }
  )
  
  const stage = new Stage()
  stage.add(formulaGrid)
  stage.add(traceGrid)
  stage.render(svg, document)
  
  // ? how to render transition arrows between states? 

  
  
  
  
  
  
  
  