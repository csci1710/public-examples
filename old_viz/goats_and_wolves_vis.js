const animal1 = Goat
const url1 = 'https://i.pinimg.com/originals/f8/01/e4/f801e4c0be2ef6505f099093a15ae2d8.jpg'
const animal2 = Wolf
const url2 = 'https://www.how-to-draw-funny-cartoons.com/images/wolf-clipart-004.png'

const boat_url = 'https://www.pngkey.com/png/detail/487-4876007_canoe-paddle-clipart-yellow-boat-clip-art-row.png'
const arrow_url = 'http://clipart-library.com/images/pcodGR6ei.png'

function get_animal_position(animal,st){
  const ans = animal.join(st.join(gwshore)).toString() ; 
  if(st.toString() == "GWState4"){
    console.log("animal ",animal.toString()," has pos ",ans);
  } 
  return ans; 

}
function make_animal(url) {
  const img = document.createElement('img')
  img.src = url
  img.style.width = '100%'
  img.style.height = '15%'
  img.style.display = 'block'
  img.style['margin-bottom'] = '10%'

  return img;
}

function make_blank() {
  const div = make_animal('https://wallpapercave.com/wp/wp2831956.png')
  div.style.opacity = '0%'
  return div
}


function make_boat(side) {
  const boat_img = document.createElement('img')
  boat_img.src = boat_url
  boat_img.style.width = '20%'
  boat_img.style['margin-left'] = '5%'
  boat_img.style['margin-right'] = '5%'
  
  if (side.startsWith('Near')) {
    boat_img.style.float = 'left'
    
  } else {
    boat_img.style.float = 'right'
    boat_img.style.transform = 'scaleX(-1)';
  }
  
  return boat_img
}

function make_arrow(direction) {
  const arrow_img = document.createElement('img')
  arrow_img.src = arrow_url
  arrow_img.style.width = '90%'
  arrow_img.style.height = '12%'
  arrow_img.style['margin-bottom'] = '10%'
  arrow_img.style['margin-left'] = '5%'
  arrow_img.style['margin-right'] = '5%'
  
  if (direction === "left") {
    arrow_img.style.float = 'left'
    arrow_img.style.transform = 'scaleX(-1)';
  } else {
    arrow_img.style.float = 'right'
  }
  
  return arrow_img
}

div.replaceChildren() // remove all content

let state = GWState;
while (gwnext.join(state).tuples().length > 0) {
  state = gwnext.join(state)
}
let i = 0; 
do {
  const pre = state;
  const post = state.join(gwnext)
  const side = state.join(gwboat).tuples()[0].toString();

  function shift_near_far(animal){
   return get_animal_position(animal,pre).includes(Near.toString()) &&
     get_animal_position(animal,post).includes(Far.toString())
  }
  function to_move(animal, dir) {
    if(post.toString()=="") {return ; }
     return get_animal_position(animal,post) != get_animal_position(animal,pre)
    
  }
  
  function make_side(side, side_str) {
    const div = document.createElement('div')
    div.style.width = '16%'
    div.style.height = '100%'
    div.style.float = side_str
    
   
    for (const ind in animal1.tuples()) {
      const animal = animal1.tuples()[ind]
      const on_side = get_animal_position(animal,state).includes(side.toString());
      if (on_side) {
        div.appendChild(make_animal(url1))
      } else {
        div.appendChild(make_blank())
      }
    }
    
    for (const ind in animal2.tuples()) {
      const animal = animal2.tuples()[ind]
     
      const on_side = get_animal_position(animal,state).includes(side.toString());
      if (on_side) {
        div.appendChild(make_animal(url2))
      } else {
        div.appendChild(make_blank())
      }
    }
    
    
    return div
    
  }

  function make_arrows() {
    const div = document.createElement('div')
    div.style.width = '60%'
    div.style.height = '100%'
    div.style.float = 'left'

    const dir = side.startsWith('Near') ? 'right' : 'left'

    for (const animal of animal1.tuples()) {
      let arr = make_arrow(dir);
      if (!to_move(animal, dir)) {
        arr.style.opacity = '0%'
      }

      div.appendChild(arr);
    }

    for (const animal of animal2.tuples()) {
      let arr = make_arrow(dir);
      if (!to_move(animal, dir)) {
        arr.style.opacity = '0%'
      }

      div.appendChild(arr);
    }

    return div;
  }
  
  const near_div = make_side(Near, 'left')
  

  const arrow_div = make_arrows()
  const far_div = make_side(Far, 'right')
  

  // const boat_div = make_boat(side)
  
  const pree = document.createElement('pre')
  pree.style.width = '23%'
  pree.style.height = '30%'
  pree.style.margin = '1%'
  pree.style.marginRight = '0'
  pree.style.padding = '0.5em'
  pree.style.border = '1px solid black'
  pree.style.display = 'inline-block'
  pree.style.color = 'white'
  pree.style["background-color"] = 'gray'
  
  pree.appendChild(near_div)
  pree.appendChild(far_div)
  //pree.appendChild(boat_div)
  pree.appendChild(arrow_div)
  
  div.appendChild(pree)
  
  
  state = state.join(gwnext);
  i++;
} while (state.tuples()[0]);
