```
                                                                       
     client.c will be de-monolithed in the future, probably after alexd
     has done his own separating of tinyUSB                            
+----------+                                                           
| client.c |                                                           
+----------+                         +----------+                      
                                     | client.c |                      
                                     +----------+                      
                                    +------------+                     
                                    | hid_host.c |                     
                                    +------------+                     
                                                                       
  +-------+                           +--------+                       
  | usb.c | <----> tinyusb source:    | usbh.c |                       
  +-------+                           +--------+                       
      |                                                                
      v                               +--------+                       
 +--------+                           | ehci.c |                       
 | pcie.c |                           +--------+                       
 +--------+                                                            
```
