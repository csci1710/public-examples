// Create the stage object to contain our scene
const stage = new Stage()
// Give ourselves enough vertical space. If visualization gets 
// truncated, change this! You can also adjust style.width.
document.getElementById('svg-container').style.height = '1100%'

/////////////////////////////////////////////////////////////////////
// Handle all states
/////////////////////////////////////////////////////////////////////

// Create a grid object that contains one cell per state
//    `instances` is an array that contains the states
const stateGridConfig = {
    grid_location :{
        x:10,
        y:10
    },
    cell_size:{
        x_size:300,
        y_size:300
    },
    grid_dimensions:{
        y_size: instances.length,
        x_size:2
    }
  }

const statesGrid = new Grid(stateGridConfig)

// For every instance, place a visualization in the proper grid location
instances.forEach( (inst, idx) => {    
    const lb = idx == loopBack ? " (loopback)" : ""
    statesGrid.add({x:0, y:idx}, new TextBox(`State:${idx}${lb}`,{x:0,y:0},'black',16))
    statesGrid.add({x:1, y:idx}, visualizeStateAsText(inst, idx))    
})

/////////////////////////////////////////////////////////////////////
// Handle each individual state
/////////////////////////////////////////////////////////////////////

function visualizeStateAsText(inst, idx) {
    // The set of smiths present in this instance (which should, technically, never change)
    const theseSmiths = inst.signature('Smith').atoms()
    // The set of chopsticks present in this instance (which also should never change)
    const theseChops = inst.signature('Chopstick').atoms()
    // The value of clean, requested, etc. in this state. We must work with _ids_, not with atoms
    //   if we plan to check for membership in these arrays (and we do), since two atoms may be
    //   different *JavaScript* objects, yet represent the same "object" in the instance.
    const nowCleanIDs = inst.signature('Table').join(inst.field('clean')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const nowRequestedIDs = inst.signature('Table').join(inst.field('requested')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const nowHoldingLeftIDs = inst.signature('Table').join(inst.field('holdingLeft')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const nowHoldingRightIDs = inst.signature('Table').join(inst.field('holdingRight')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()

    const group = new Grid({
        grid_location :{
            x:10,
            y:10
        },
        cell_size:{
            x_size:130,
            y_size:40
        },
        grid_dimensions:{
            y_size: Math.max(theseSmiths.length, theseChops.length),
            x_size:2
        }
      })

    theseSmiths.forEach( (sm, smithIdx) => { 
        const leftStr = nowHoldingLeftIDs.includes(sm.id()) ? "L" : ""
        const rightStr = nowHoldingRightIDs.includes(sm.id()) ? "R" : ""
        group.add({x:0, y:smithIdx}, new TextBox(`${sm}:${leftStr},${rightStr}`,{x:0,y:0},'black',16))
    })
    theseChops.forEach( (ch, chopIdx) => {
        const cleanStr = nowCleanIDs.includes(ch.id()) ? "C" : ""
        const requestedStr = nowRequestedIDs.includes(ch.id()) ? "R" : ""
        group.add({x:1, y:chopIdx}, new TextBox(`${ch}:${cleanStr},${requestedStr}`,{x:0,y:0},'black',16))
    })
    
    
    return group
}


// Finally, add the grid to the stage and render it:
stage.add(statesGrid)
stage.render(svg, document)