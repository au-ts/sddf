from .backends import OUTPUT

def info(s):
    OUTPUT.write("CI|INFO: " + s + "\n")

def error(s):
    OUTPUT.write("CI|ERROR: " + s + "\n")
