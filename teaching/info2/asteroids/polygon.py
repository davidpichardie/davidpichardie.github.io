# -*- coding: utf-8 -*-
from __future__ import print_function, division
from point import Point
import pygame
import math

class Polygon:

    def __init__(self, shape, color, offset, rotation):
        if len(shape)==0:
            raise ValueError
        
        self.shape = shape[:]
        self.offset = offset
        self.rotation = rotation
        self.color = color
        
        origin = shape[0].copy()
        for p in self.shape:
            if p.x < origin.x:
                origin.x = p.x
            if p.y < origin.y:
                origin.y = p.y

        # attention, nous modifions le parametre de la méthode !!
        for p in self.shape:
            p.x = p.x - origin.x
            p.y = p.y - origin.y

    def rotate(self, angle):
        self.rotation = (self.rotation + angle) % 360
            
    def translate(self, p):
        self.offset.x = self.offset.x + p.x
        self.offset.y = self.offset.y + p.y
            
    def get_points(self):
        def area():
            sum = 0
            j = 1
            for i in range(len(self.shape)):
                sum += self.shape[i].x*self.shape[j].y \
                       - self.shape[j].x*self.shape[i].y
                j = (j+1) % len(self.shape)
            return abs(sum/2)
        def center():
            x,y = 0,0
            j = 1
            for i in range(len(self.shape)):
                f = self.shape[i].x * self.shape[j].y \
                    - self.shape[j].x * self.shape[i].y 
                x += (self.shape[i].x + self.shape[j].x) * f
                y += (self.shape[i].y + self.shape[j].y) * f
                j = (j+1) % len(self.shape)
            a = area ()
            return Point(abs(x/(6*a)),abs(y/(6*a)))
        r = math.radians(self.rotation)
        c = center()
        res = []
        for p in self.shape:
            x = (p.x-c.x) * math.cos(r) - (p.y-c.y) * math.sin(r) \
                + c.x + self.offset.x
            y = (p.x-c.x) * math.sin(r) + (p.y-c.y) * math.cos(r) \
                + c.y + self.offset.y
            p2 = Point(x,y)
            res.append(p2)
        return res

    def paint(self,canvas):
        height = canvas.screen.get_rect().height
        width = canvas.screen.get_rect().width
        def min_x(points):
            min = points[0][0]
            for p in points:
                if min > p[0]:
                    min = p[0]
            return min
    
        def min_y(points):
            min = points[0][1]
            for p in points:
                if min > p[1]:
                    min = p[1]
            return min
    
        def max_x(points):
            max = points[0][0]
            for p in points:
                if max < p[0]:
                    max = p[0]
            return max
    
        def max_y(points):
            max = points[0][1]
            for p in points:
                if max < p[1]:
                    max = p[1]
            return max
        
        def wrap(x,h):
            if x<0: return x+h
            elif x>h: return x-h
            else: return x

        self.offset.x = wrap(self.offset.x,width)
        self.offset.y = wrap(self.offset.y,height)
        
        points = self.get_points()
        couples = [(int(p.x),height-int(p.y)) for p in points]
        all = [couples]
        if min_x(couples) < 0:
            all.append([(x+width,y) for (x,y) in couples])
        if max_x(couples) > width:
            all.append([(x-width,y) for (x,y) in couples])
        if min_y(couples) < 0:
            all.append([(x,y+height) for (x,y) in couples])
        if max_y(couples) > height:
            all.append([(x,y-height) for (x,y) in couples])
        for c in all:
            pygame.draw.polygon(canvas.background,self.color,tuple(c))

    def contains_point(self,p):
        points = self.get_points()
        crossingNumber = 0
        j = 1
        for i in range(len(self.shape)):
            if (((points[i].x < p.x and p.x <= points[j].x) or \
                 (points[j].x < p.x and p.x <= points[i].x)) and \
                (p.y > points[i].y + \
                 (points[j].y-points[i].y)/ \
                 (points[j].x - points[i].x) * (p.x - points[i].x))): 
                crossingNumber += 1
            j=(j+1) % len(self.shape)
        return crossingNumber % 2 == 1

    def contains_polygone(self,poly):
        points = poly.get_points()
        for p in points:
            if self.contains_point(p):
                return True
        return False

    def get_nth(self,i):
        points = self.get_points()
        if i >= len(points):
            raise ValueError
        return points[i]
