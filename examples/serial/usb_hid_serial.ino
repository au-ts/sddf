#include <Usb.h>
#include <KeyboardController.h>
#define private public
#include <MouseController.h>
#undef private

/**
 * Protocol:
 * 
 * Each byte is 8 bits, the high bits indicates the start for self-synchronising.
 *    (reader can wait til the next high bit)
 *    
 * This gives us 7 bits to work with in each byte.
 * 
 * First byte (with the high bit) is the command.
 *  0x0: key press, following byte is (oem) key.
 *  0x1: key release, following byte is (oem) key
 *  0x2: mouse key press change (following is mouse buttons)
 *  0x3: mouse move (following is 10 bytes of 2x32 (dx then dy) bits int in 7 bits)
 * 
 */

USBHost usb;
// the order matters because of course it does
// only one at a time
KeyboardController keyboard(usb);
MouseController mouse(usb);


typedef enum cmd {
  Cmd_KeyPress = 0x0,
  Cmd_KeyRelease = 0x1,
  Cmd_MouseKeyChange = 0x2,
  Cmd_MouseMove = 0x3,
} cmd_t;


void send(cmd_t cmd, uint8_t data[]) {
  Serial.write(cmd | 0x80);
  
  switch (cmd) {
    case Cmd_KeyPress:
    case Cmd_KeyRelease:
    case Cmd_MouseKeyChange:
      Serial.write(data[0] & ~0x80);
      break;
    case Cmd_MouseMove:
      Serial.write(data[0] & ~0x80);
      Serial.write(data[1] & ~0x80);
      Serial.write(data[2] & ~0x80);
      Serial.write(data[3] & ~0x80);
      Serial.write(data[4] & ~0x80);
      Serial.write(data[5] & ~0x80);
      Serial.write(data[6] & ~0x80);
      Serial.write(data[7] & ~0x80);
      Serial.write(data[8] & ~0x80);
      Serial.write(data[9] & ~0x80);
      break;
  }
}

void keyPressed() {
  uint8_t key = keyboard.getOemKey();
  // Sending the OEM key directly as the library's support for
  // decoding it is broken and sometimes just emits nothing.
  // This gives us a single character value on serial.
  // It looks like garbage, though.
  uint8_t data[1] = {key};
  send(Cmd_KeyPress, data);

// For debugging
//  Serial.print(" key:");
//  Serial.print(keyboard.getKey());
}

void keyReleased() {
  uint8_t key = keyboard.getOemKey();
  uint8_t data[1] = {key};
  send(Cmd_KeyRelease, data);
}

void mousePressed() {
  uint8_t buttons = mouse.buttons;
  uint8_t data[1] = {buttons};
  send(Cmd_MouseKeyChange, data);
}

void mouseReleased() {
  uint8_t buttons = mouse.buttons;
  uint8_t data[1] = {buttons};
  send(Cmd_MouseKeyChange, data);
}

void mouseDragged() {
  mouseMoved();
}

void mouseMoved() {
  // only allow 7 bits per byte.
  int dx = mouse.getXChange();
  int dy = mouse.getYChange();
  uint8_t data[10] = {
    ((dx >> (0*7)) & 0x7f), ((dx >> (1*7)) & 0x7f), ((dx >> (2*7)) & 0x7f), ((dx >> (3*7)) & 0x7f), ((dx >> (4*7)) & 0x7f),
    ((dy >> (0*7)) & 0x7f), ((dy >> (1*7)) & 0x7f), ((dy >> (2*7)) & 0x7f), ((dy >> (3*7)) & 0x7f), ((dy >> (4*7)) & 0x7f),
  };
  send(Cmd_MouseMove, data);
}

void setup() {
  Serial.begin(115200);
}

void loop() {
  usb.Task();
}
