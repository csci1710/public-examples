d3 = require('d3')
d3.selectAll("svg > *").remove();

STATE_HEIGHT = 100
START_STATES = 100

states = 
     d3.select(svg)
     .selectAll('g') 
     .data(instances.map(function(d,i) {        
        return {item: d, index: i}    
     }))     
     .enter()        
     .append('g') 
     .classed('state', true)     
     .attr('id', d => d.index)        
states
    .append('rect')
    .attr('x', 10)
    .attr('y', function(d) {
         return START_STATES + STATE_HEIGHT * d.index
     })
    .attr('width', 400)
    .attr('height', STATE_HEIGHT)
    .attr('stroke-width', 2)
    .attr('stroke', 'black')
    .attr('fill', 'transparent');
states
    .append("text")
    .style("fill", "black")
     .attr('y', function(d) {
         return START_STATES + 20 + STATE_HEIGHT * d.index
     })
     .attr('x', 50)
     .text(d => "State "+d.index);

states
    .append("text")
    .style("fill", "black")
    .attr('y', function(d) {
         return START_STATES + 60 + STATE_HEIGHT * d.index
     })
    .attr('x', function(triple) {
         return 50 
     })
     .text(d => buildList(d.item, d.index))    

function buildList(inst, idx) {
    // IMPORTANT: you cannot safely write "Stoplight.root" or 
    //   "Stoplight.join(root)" like you would in a non-temporal model. 
    // Instead, need to isolate the fields for this particular state:
    const root_rel = instances[idx].field('root')        
    const stoplight_rel = instances[idx].signature('Stoplight')
    const next_rel = instances[idx].field('next')
   
    const root_set = stoplight_rel.join(root_rel)
    // BEWARE: JavaScriot arrays have a join() method. This means that
    // if you accidentally do root_set.tuples().join(...) instead of 
    // root_set.join(...) you'll get no error, and probably get a surprising 
    // empty string somewhere.   
    if(root_set.tuples().length < 1) 
        return "No cars in queue"
    else 
        handleNext = root_set
        buildString = "Cars Queue: "
        while(handleNext.tuples().length > 0) {
            buildString += handleNext.tuples()[0] + ", "
            // BEWARE: Sterling doesn't give "empty join" errors.
            // This commented-out line will run, but always be empty since the
            // first column of next_rel is a Stoplight.
            //handleNext = handleNext.join(next_rel)
            handleNext = handleNext.join(stoplight_rel.join(next_rel))                     
        }        
        return buildString 
}

