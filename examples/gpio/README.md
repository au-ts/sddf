# TODO

build a client
 - idk what fucntionality to provide yet but potentially driving an led sounds easy for an output example
 - then have an input example such as pressing a button
 - dont have to test every gpio pin because that just proves the intialisation function is correct

get driver and virt working together

then start adding to other device classes like gpio

convert enums to defines or vice versa

change it so that instead of functions as an array, its just a struct of each individual function

# see what peter says about design

# do the irqs need to be edge?

# go back and try remove repeated code

# solve the problem where someone assigns a gpio to an irq channel successfully
ie they have permissions for both
now they want to disconnect from the irq channel which they do successfully
however now the irq channel still holds the value of the pin from before
so someone can come along and claim it (with the gpio pin still selected)
now they have access to the infomation

there does appear to be empty values 100:223 that we can assign to the pins
hence we could always default back to or have the option to set to that

theres another situation as well when a clinet releases a gpio pin while they have an irq still configured to it
so now they could wait for someone to come along and claim it and thus the original client could
listen to it

## are all of the SELECT GPIO PIN FOR irq stuff initiated to 0
because if so then theoretically all of them would be intially mapped to AO pin 0
this ties into the example where i need a button