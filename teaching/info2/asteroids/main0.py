# -*- coding: utf-8 -*-
from __future__ import print_function, division
from polygon import Polygon
from point import Point
from canvas import Canvas
import pygame
import math


def game():
    width = 480
    height = 640
    canvas = Canvas(width,height) 

    shape = [Point(0,0), Point(30,10), Point(0,20)]
    blue = (0,0,255)
    poly = Polygon(shape,blue,Point(width/2,height/2),90)

    clock = pygame.time.Clock() #horloge du jeu
    mainloop = True
    FPS = 30 # vitesse max d'animation
    
    while mainloop:
        milliseconds = clock.tick(FPS)  # tick d'horloge
        seconds = milliseconds / 1000.0 # [seconds] secondes ont passé depuis la derniere boucle
 
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                # fenetre ferméee par le joueur
                mainloop = False 
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    mainloop = False 
                if event.key == pygame.K_UP:
                    poly.translate(Point(0,10))
                if event.key == pygame.K_DOWN:
                    poly.translate(Point(0,-10))
                if event.key == pygame.K_RIGHT:
                    poly.translate(Point(10,0))
                if event.key == pygame.K_LEFT:
                    poly.translate(Point(-10,0))

        pygame.display.set_caption("[FPS]: %.2f" % clock.get_fps())
        
        canvas.clear()
        poly.paint(canvas)
        canvas.redraw()

if __name__ == "__main__":
    game()
